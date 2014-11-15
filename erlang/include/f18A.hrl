% RECORDS

-record(cpu,{ id,
              channel,
              rom,
              ram,
              io,
              p,
              r,
              rs = [0,0,0,0,0,0,0,0],
              a,
              b,
              i  = [],
              t  = 0,
              s  = 0,
              ds = [0,0,0,0,0,0,0,0],
              carry = 0,
              breakpoints = []
            }).

