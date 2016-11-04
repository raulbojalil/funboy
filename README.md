# Funboy

A Gameboy Emulator written in F#.

My goal was to write a Gameboy emulator using the fewest lines of code possible, while
still being readable (I hope). I used this project to improve my F# skills (my new favorite language BTW), 
so there may be some beginner or poorly written code. 
There are some features missing, most notably sound support.
To keep it simple, I used WinForms/GDI+ drawing, which is slow but good enough for my purposes.

To run you will need to download install the F# runtime from the Microsoft website.

You can run it as a script or compile to an exe file using the following commands:

"C:\Program Files (x86)\Microsoft F#\v4.0\fsi.exe" ChipF.fsx (to run as a script)
"C:\Program Files (x86)\Microsoft F#\v4.0\fsc.exe" ChipF.fsx (to compile to an exe file)

![Funboy](https://github.com/raulbojalil/funboy/blob/master/screenshot.png?raw=true "Funboy")
![Funboy](https://github.com/raulbojalil/funboy/blob/master/tileviewer.png?raw=true "Funboy")
![Funboy](https://github.com/raulbojalil/funboy/blob/master/mapviewer.png?raw=true "Funboy")