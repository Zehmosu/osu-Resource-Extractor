attribute vec2 m_Position;
attribute vec2 m_TexCoord;
attribute float m_Time;

varying vec4 v_Colour;
varying vec2 v_TexCoord;

uniform mat4 g_ProjMatrix;
uniform float g_FadeClock;

void main(void)
{
	gl_Position = g_ProjMatrix * vec4(m_Position, 1.0, 1.0);
	v_Colour = vec4(1.0, 1.0, 1.0, m_Time - g_FadeClock);
	v_TexCoord = m_TexCoord;
}