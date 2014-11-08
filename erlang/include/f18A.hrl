% RECORDS

-record(cpu,{ id,
              channel,
              rom,
              ram,
              io,
              p,
              a,
              b,
              i           = [],
              t           = 0,
              breakpoints = []
            }).

