% RECORDS

-record(cpu,{ id,
              channel,
              rom,
              ram,
              io,
              p,
              a,
              b,
              i = [],
              s = 0,
              t = 0,
              breakpoints = []
            }).

