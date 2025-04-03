# todo.md

- add previously unused axi signals to all axi modules, eg. awcache, etc. These
  need to be set when interfacing with vivado mig gen'd axi interfaces.
- test bench for svc_pix_cdc (although, this gets a workout in the example repo)
- test bench for svc_fb_vga (although, this gets a workout in the example repo)
- optimized versions of the axi modules that currently use burst_iter or ax_iter
  when we know the len will always be 1. (They can wrap this optimized version)
- rename the axi null to null_m and make an_s version too.
- make axil versions of null
