import os
import sys
import clr
import logging
from datetime import datetime
import io
import shutil
from typing import List, Optional, Tuple, Dict, Any
import traceback
import xml.etree.ElementTree as ET
import base64
import glob
import winreg
from tkinter import Tk
from tkinter import filedialog

# Required .NET assemblies (Literally won't work without xd)
clr.AddReference('System.Drawing')
clr.AddReference('System.Windows.Forms')
clr.AddReference('System.Resources.ResourceManager')
clr.AddReference('System.Resources.Reader')

import System
from System.IO import File, MemoryStream, Directory, Path, BinaryReader, SeekOrigin
from System.Drawing import Image as DrawingImage
from System.Drawing.Imaging import ImageFormat, PixelFormat
from System.Resources import ResourceReader, ResourceSet
from System.Globalization import CultureInfo
from PIL import Image

class ResourceExtractor:
    # ResX/XML parsing related constants
    RESX_HEADER = '''<?xml version="1.0" encoding="utf-8"?>
<root>
  <xsd:schema id="root" xmlns="" xmlns:xsd="http://www.w3.org/2001/XMLSchema" xmlns:msdata="urn:schemas-microsoft-com:xml-msdata">
    <xsd:element name="root" msdata:IsDataSet="true">
      <xsd:complexType>
        <xsd:choice maxOccurs="unbounded">
          <xsd:element name="metadata">
            <xsd:complexType>
              <xsd:sequence>
                <xsd:element name="value" type="xsd:string" minOccurs="0" />
              </xsd:sequence>
              <xsd:attribute name="name" use="required" type="xsd:string" />
              <xsd:attribute name="type" type="xsd:string" />
              <xsd:attribute name="mimetype" type="xsd:string" />
              <xsd:attribute ref="xml:space" />
            </xsd:complexType>
          </xsd:element>
          <xsd:element name="assembly">
            <xsd:complexType>
              <xsd:attribute name="alias" type="xsd:string" />
              <xsd:attribute name="name" type="xsd:string" />
            </xsd:complexType>
          </xsd:element>
          <xsd:element name="data">
            <xsd:complexType>
              <xsd:sequence>
                <xsd:element name="value" type="xsd:string" minOccurs="0" msdata:Ordinal="1" />
                <xsd:element name="comment" type="xsd:string" minOccurs="0" msdata:Ordinal="2" />
              </xsd:sequence>
              <xsd:attribute name="name" type="xsd:string" use="required" msdata:Ordinal="1" />
              <xsd:attribute name="type" type="xsd:string" msdata:Ordinal="3" />
              <xsd:attribute name="mimetype" type="xsd:string" msdata:Ordinal="4" />
              <xsd:attribute ref="xml:space" />
            </xsd:complexType>
          </xsd:element>
          <xsd:element name="resheader">
            <xsd:complexType>
              <xsd:sequence>
                <xsd:element name="value" type="xsd:string" minOccurs="0" msdata:Ordinal="1" />
              </xsd:sequence>
              <xsd:attribute name="name" type="xsd:string" use="required" />
            </xsd:complexType>
          </xsd:element>
        </xsd:choice>
      </xsd:complexType>
    </xsd:element>
  </xsd:schema>
  <resheader name="resmimetype">
    <value>text/microsoft-resx</value>
  </resheader>
  <resheader name="version">
    <value>2.0</value>
  </resheader>
  <resheader name="reader">
    <value>System.Resources.ResXResourceReader, System.Windows.Forms, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089</value>
  </resheader>
  <resheader name="writer">
    <value>System.Resources.ResXResourceWriter, System.Windows.Forms, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089</value>
  </resheader>
'''

    # File signatures for various formats
    FILE_SIGNATURES = {
        # Images 
        b'\x89PNG\r\n\x1a\n': '.png',
        b'BM': '.bmp',
        b'\xFF\xD8\xFF': '.jpg',
        b'GIF87a': '.gif',
        b'GIF89a': '.gif',
        # Sprites
        b'\x00\x00\x01\x00': '.ico',
        # Audio
        b'RIFF': '.wav',
        b'OggS': '.ogg', 
        b'\xFF\xFB': '.mp3',
        b'ID3': '.mp3',
        # Fonts
        b'\x00\x01\x00\x00\x00': '.ttf',
        b'OTTO': '.otf',
        b'true': '.ttf',
        b'typ1': '.ttf',
        # Shader/Code indicators
        b'#version': '.glsl',
        b'void main': '.glsl',
        b'uniform': '.glsl',
        b'varying': '.glsl',
        b'precision': '.glsl',
        # Archive formats
        b'PK\x03\x04': '.zip',
        b'\x1F\x8B\x08': '.gz',
        b'7z\xBC\xAF\x27\x1C': '.7z',
        # Video formats
        b'\x00\x00\x00\x18ftypmp42': '.mp4',
        b'\x00\x00\x00\x14ftypqt  ': '.mov'
    }
    
    # Shader file patterns and their corresponding extensions
    SHADER_PATTERNS = {
        'sh_': {
            '_vs': '.vert',    # Vertex shader
            '_fs': '.frag',    # Fragment shader
            '_gs': '.geom',    # Geometry shader
            '_cs': '.comp',    # Compute shader
            '_h': '.glsl',     # Header shader
            '_2D': '.glsl',    # 2D shader
            '_3D': '.glsl',    # 3D shader
        }
    }
    
    # Common shader keywords that help identify shader files
    SHADER_KEYWORDS = [
        b'uniform',
        b'varying',
        b'attribute',
        b'gl_Position',
        b'gl_FragColor',
        b'texture2D',
        b'vec2',
        b'vec3',
        b'vec4',
        b'mat2',
        b'mat3',
        b'mat4'
    ]

    PNG_CHUNK_TYPES = [b'IHDR', b'IDAT', b'PLTE', b'IEND', b'tRNS', b'cHRM', b'gAMA', 
                      b'sBIT', b'sRGB', b'tEXt', b'zTXt', b'iTXt', b'bKGD', b'pHYs', 
                      b'sPLT', b'hIST', b'tIME']

    def __init__(self, output_dir: str, log_file: Optional[str] = None):
        self.output_dir = output_dir
        self.temp_dir = os.path.join(output_dir, "temp")
        os.makedirs(self.temp_dir, exist_ok=True)
        self.setup_logging(log_file)
        self.resource_names = {}  # Store resource names from XML

    def setup_logging(self, log_file: Optional[str]) -> None:
        self.logger = logging.getLogger('ResourceExtractor')
        self.logger.setLevel(logging.DEBUG)
        
        formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        
        if log_file:
            file_handler = logging.FileHandler(log_file)
            file_handler.setFormatter(formatter)
            self.logger.addHandler(file_handler)
            
        console_handler = logging.StreamHandler()
        console_handler.setFormatter(formatter)
        self.logger.addHandler(console_handler)

    def find_resource_names(self, binary_data: bytes) -> dict:
        """Extract resource names and types from XML/ResX data in binary"""
        names_dict = {}
        try:
            # Find XML data
            xml_start = binary_data.find(b'<?xml')
            if xml_start != -1:
                xml_end = binary_data.find(b'</root>', xml_start)
                if xml_end != -1:
                    xml_end += 7  # Include '</root>'
                    xml_data = binary_data[xml_start:xml_end]
                    
                    # Try both UTF-16 and UTF-8 encodings
                    for encoding in ['utf-16', 'utf-8']:
                        try:
                            xml_str = xml_data.decode(encoding)
                            root = ET.fromstring(xml_str)
                            
                            # Process all resource data elements
                            for data_elem in root.findall('.//data'):
                                name = data_elem.get('name')
                                mime_type = data_elem.get('mimetype', '')
                                type_attr = data_elem.get('type', '')
                                
                                value_elem = data_elem.find('value')
                                if name and value_elem is not None:
                                    if value_elem.text:
                                        try:
                                            # Handle base64 encoded data
                                            if 'base64' in mime_type.lower() or 'System.Byte[]' in type_attr:
                                                value_text = value_elem.text.strip()
                                                # Add padding if needed
                                                padding = 4 - (len(value_text) % 4)
                                                if padding != 4:
                                                    value_text += '=' * padding
                                                decoded = base64.b64decode(value_text)
                                                
                                                # Store first 50 bytes as key for matching
                                                names_dict[decoded[:50]] = {
                                                    'name': name,
                                                    'mime_type': mime_type,
                                                    'type': type_attr,
                                                    'file_type': self.detect_file_type(decoded, name)
                                                }
                                                
                                            # Handle other resource types
                                            else:
                                                names_dict[name] = {
                                                    'name': name,
                                                    'mime_type': mime_type,
                                                    'type': type_attr,
                                                    'value': value_elem.text
                                                }
                                                
                                        except Exception as e:
                                            self.logger.debug(f"Error processing resource {name}: {str(e)}")
                                            continue
                            
                            if names_dict:
                                break
                                
                        except Exception as e:
                            continue
                            
        except Exception as e:
            self.logger.error(f"Error extracting resource names: {str(e)}")
            
        return names_dict

    def detect_shader_content(self, data: bytes) -> bool:
        """Check if content appears to be a shader"""
        try:
            # Try to decode as text
            text = data.decode('utf-8')
            
            # Check for common shader keywords
            for keyword in self.SHADER_KEYWORDS:
                if keyword in data:
                    return True
                    
            # Check for typical shader structure
            if ('void main' in text and 
                ('{' in text and '}' in text) and
                any(word in text for word in ['uniform', 'varying', 'gl_', 'texture2D'])):
                return True
                
        except UnicodeDecodeError:
            pass
            
        return False

    def detect_file_type(self, data: bytes, name: str = "") -> Optional[str]:
        """Detect file type from binary data and name"""
        # Check shader patterns in filename first
        if name:
            for prefix, patterns in self.SHADER_PATTERNS.items():
                if name.startswith(prefix):
                    for suffix, ext in patterns.items():
                        if suffix in name:
                            if self.detect_shader_content(data):
                                return ext
                            # Even if content doesn't look like a shader, trust the naming pattern
                            return ext
        
        # Check for common file signatures
        for signature, extension in self.FILE_SIGNATURES.items():
            if data.startswith(signature):
                return extension
        
        # Additional checks for PNG validity
        if data.startswith(b'\x89PNG\r\n\x1a\n'):
            if self.validate_png(data):
                return '.png'
        
        # Check if content looks like a shader
        if self.detect_shader_content(data):
            return '.glsl'
        
        # Try to detect image format using PIL
        try:
            with Image.open(io.BytesIO(data)) as img:
                return '.' + img.format.lower()
        except:
            pass
        
        # Try to detect text-based files
        try:
            text = data.decode('utf-8')
            # Check for XML
            if text.strip().startswith('<?xml'):
                return '.xml'
            # Check for JSON
            if text.strip().startswith('{') and text.strip().endswith('}'):
                return '.json'
            # Check for plain text
            if text.isprintable() and len(text.split()) > 1:
                return '.txt'
        except:
            pass
        
        # Check for .NET serialized data
        if b'System.Drawing.Bitmap' in data:
            return '.png'  # Assume it's a serialized PNG
            
        return None

    def validate_png(self, data: bytes) -> bool:
        """Validate PNG data structure"""
        try:
            pos = 8  # Skip PNG signature
            while pos < len(data):
                if pos + 8 > len(data):
                    return False
                    
                chunk_length = int.from_bytes(data[pos:pos+4], 'big')
                chunk_type = data[pos+4:pos+8]
                
                if chunk_type == b'IEND':
                    return True
                    
                if chunk_type not in self.PNG_CHUNK_TYPES:
                    return False
                    
                pos += chunk_length + 12
                
            return False
        except:
            return False

    def save_resource(self, data: bytes, name: str, output_dir: str) -> None:
        """Save resource with proper type detection"""
        try:
            # Detect file type using both content and name
            file_type = self.detect_file_type(data, name)
            if not file_type:
                # Try harder to identify shader files
                if 'sh_' in name:
                    file_type = '.glsl'
                else:
                    self.logger.debug(f"Unknown file type for {name}")
                    return

            # Create safe filename
            safe_name = "".join(c for c in name if c.isalnum() or c in ".-_ ")
            output_path = os.path.join(output_dir, f"{safe_name}{file_type}")
            
            # Ensure directory exists
            os.makedirs(os.path.dirname(output_path), exist_ok=True)
            
            # For images, validate with PIL
            if file_type in ['.png', '.jpg', '.jpeg', '.gif', '.bmp']:
                temp_path = os.path.join(self.temp_dir, f"{safe_name}_temp{file_type}")
                
                with open(temp_path, 'wb') as f:
                    f.write(data)
                    
                try:
                    with Image.open(temp_path) as img:
                        img.save(output_path)
                    self.logger.info(f"Saved image: {name}{file_type}")
                    return
                except Exception as e:
                    self.logger.debug(f"Failed to verify image {name}: {str(e)}")
            
            # Handle .NET serialized PNGs
            if b'System.Drawing.Bitmap' in data:
                try:
                    # Extract the actual PNG data
                    png_start = data.index(b'\x89PNG\r\n\x1a\n')
                    png_data = data[png_start:]
                    
                    with open(output_path, 'wb') as f:
                        f.write(png_data)
                    
                    self.logger.info(f"Saved .NET serialized PNG: {name}.png")
                    return
                except Exception as e:
                    self.logger.debug(f"Failed to extract .NET serialized PNG {name}: {str(e)}")
            
            # For other files, save directly
            with open(output_path, 'wb') as f:
                f.write(data)
                
            self.logger.info(f"Saved: {name}{file_type}")
            
        except Exception as e:
            self.logger.error(f"Error saving resource {name}: {str(e)}")

    def get_osu_installation_directory(self) -> str:
        """Retrieve the osu! installation directory from the registry."""
        key_name1 = r'SOFTWARE\Classes\osu\shell\open\command'
        key_name2 = r'SOFTWARE\Classes\osu!\shell\open\command'
        path = ''
        try:
            for key_name in [key_name1, key_name2]:
                try:
                    with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, key_name) as key:
                        path = winreg.QueryValueEx(key, '')[0]
                        if path:
                            break
                except WindowsError:
                    continue

            if path:
                path = path.split('"')[1]  # Extract path from command
                path = os.path.dirname(path)
                return path
        except Exception as e:
            self.logger.error(f"Error retrieving osu! installation directory: {str(e)}")
        return ""

    def prompt_user_for_directory(self) -> str:
        """Prompt the user to select the osu! installation directory."""
        Tk().withdraw()  # Hide the root window
        directory = filedialog.askdirectory(title="Select osu! Installation Directory")
        return directory

    def get_dll_files(self, install_dir: str) -> List[str]:
        """Get the list of DLL files from the osu! installation directory."""
        dll_files = []
        if os.path.exists(install_dir):
            dll_files = glob.glob(os.path.join(install_dir, "*.dll"))
        return dll_files

    def extract_from_dll(self, dll_path: str) -> None:
        """Extract resources from DLL"""
        try:
            self.logger.info(f"Processing DLL: {dll_path}")
            
            dll_name = Path.GetFileNameWithoutExtension(dll_path)
            output_dir = Path.Combine(self.output_dir, dll_name)
            Directory.CreateDirectory(output_dir)
            
            try:
                # Load as .NET assembly
                assembly = System.Reflection.Assembly.LoadFile(dll_path)
                resource_names = assembly.GetManifestResourceNames()
                
                for resource_name in resource_names:
                    if resource_name.endswith('.resources'):
                        self.process_resource(assembly, resource_name, output_dir)
                        
            except Exception as e:
                self.logger.warning(f"Could not load as .NET assembly: {str(e)}")
                # Try direct binary processing
                with open(dll_path, 'rb') as f:
                    binary_data = f.read()
                self.resource_names.update(self.find_resource_names(binary_data))
                
        except Exception as e:
            self.logger.error(f"Error processing DLL {dll_path}: {str(e)}")

    def process_resource(self, assembly, resource_name, output_dir):
        self.logger.info(f"Processing resource: {resource_name}")
        
        stream = assembly.GetManifestResourceStream(resource_name)
        if stream is None:
            return
            
        ms = MemoryStream()
        stream.CopyTo(ms)
        data = bytes(ms.ToArray())
        
        # First get resource names from XML
        self.resource_names.update(self.find_resource_names(data))
        
        # Process using ResourceReader
        ms.Position = 0
        reader = ResourceReader(ms)
        enumerator = reader.GetEnumerator()
        
        resource_dir = os.path.join(output_dir, 
            Path.GetFileNameWithoutExtension(resource_name))
        os.makedirs(resource_dir, exist_ok=True)
        
        while enumerator.MoveNext():
            try:
                name = enumerator.Key
                value = enumerator.Value
                
                if isinstance(value, System.Array[System.Byte]):
                    resource_data = bytes(value)
                    # Try to match with known resource names
                    resource_info = self.resource_names.get(resource_data[:50])
                    if resource_info:
                        name = resource_info['name']  # Use the name from XML
                    self.save_resource(resource_data, name, resource_dir)
                elif isinstance(value, System.Drawing.Bitmap):
                    # Handle .NET serialized bitmaps
                    ms = MemoryStream()
                    value.Save(ms, System.Drawing.Imaging.ImageFormat.Png)
                    png_data = bytes(ms.ToArray())
                    self.save_resource(png_data, name, resource_dir)
                    
            except Exception as e:
                self.logger.error(f"Error processing resource {name}: {str(e)}")
                
        ms.Dispose()
        stream.Dispose()

    def cleanup(self):
        """Clean up temporary files"""
        try:
            if os.path.exists(self.temp_dir):
                shutil.rmtree(self.temp_dir)
            self.logger.info("Cleanup completed")
        except Exception as e:
            self.logger.error(f"Error during cleanup: {str(e)}")

def cleanup_empty_directories(directory):
    for root, dirs, files in os.walk(directory, topdown=False):
        for dir_name in dirs:
            dir_path = os.path.join(root, dir_name)
            if not os.listdir(dir_path):  # Check if the directory is empty
                os.rmdir(dir_path)
                print(f"Removed empty directory: {dir_path}")

def main():
    # Configure base output directory
    base_output_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), 
                                    "extracted_resources")
    
    # Configure logging
    log_dir = os.path.join(base_output_dir, "logs")
    os.makedirs(log_dir, exist_ok=True)
    log_file = os.path.join(log_dir, f"extraction_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log")
    
    # Create extractor instance
    extractor = ResourceExtractor(base_output_dir, log_file)
    
    # Attempt to get the osu! installation directory
    install_dir = extractor.get_osu_installation_directory()
    
    # If that fails, prompt the user
    if not install_dir:
        install_dir = extractor.prompt_user_for_directory()
    
    if not install_dir:
        print("No valid installation directory provided. Exiting.")
        return

    # Get DLL files from the installation directory
    dll_files = extractor.get_dll_files(install_dir)
    
    if not dll_files:
        print("No DLL files found in the specified directory.")
        return
    
    try:
        # Process each DLL
        for dll_file in dll_files:
            try:
                extractor.extract_from_dll(dll_file)
            except Exception as e:
                extractor.logger.error(f"Failed to process {dll_file}: {str(e)}\n{traceback.format_exc()}")
        
        extractor.logger.info("Resource extraction completed!")
        extractor.cleanup()
        
        # Clean up empty directories
        cleanup_empty_directories(base_output_dir)
        
        print("Extraction process completed. Empty directories have been removed.")
        
    except Exception as e:
        extractor.logger.error(f"Error during extraction: {str(e)}")
        extractor.cleanup()

if __name__ == "__main__":
    main()