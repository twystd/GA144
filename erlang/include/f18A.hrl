% RECORDS

-record(cpu,{ id,
              channel,
              rom = array:new(64),
              ram = array:new(64),
              io,
              p,
              r  = 0,
              rs = {0,array:new(8,[{default,0}])},
              a,
              b,
              i  = [],
              t  = 0,
              s  = 0,
              ds = {0,array:new(8,[{default,0}])},
              carry = 0,

              breakpoints = [],
              log         = yes,
              trace       = yes
            }).

