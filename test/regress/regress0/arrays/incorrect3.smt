(benchmark fuzzsmt
:logic QF_AX
:status unsat
:extrafuns ((v0 Array))
:extrafuns ((v1 Index))
:extrafuns ((v2 Element))
:extrafuns ((v3 Element))
:extrafuns ((v4 Element))
:extrafuns ((v5 Element))
:extrafuns ((v6 Element))
:formula
(let (?e7 (store v0 v1 v2))
(let (?e8 (select ?e7 v1))
(let (?e9 (select ?e7 v1))
(flet ($e10 (distinct v0 v0))
(flet ($e11 (= ?e7 v0))
(flet ($e12 (distinct v1 v1))
(flet ($e13 (distinct v4 ?e9))
(flet ($e14 (distinct v2 v6))
(flet ($e15 (= ?e9 ?e9))
(flet ($e16 (distinct v2 v5))
(flet ($e17 (= v6 v5))
(flet ($e18 (= v3 v3))
(flet ($e19 (= v2 v2))
(flet ($e20 (distinct v2 v2))
(flet ($e21 (distinct v3 v4))
(flet ($e22 (distinct v4 ?e9))
(flet ($e23 (distinct v4 v5))
(flet ($e24 (= ?e9 v3))
(flet ($e25 (= v3 ?e8))
(let (?e26 (ite $e21 v0 v0))
(let (?e27 (ite $e20 ?e7 v0))
(let (?e28 (ite $e13 ?e26 v0))
(let (?e29 (ite $e22 ?e7 ?e7))
(let (?e30 (ite $e17 ?e29 ?e29))
(let (?e31 (ite $e16 ?e28 ?e28))
(let (?e32 (ite $e18 ?e29 ?e30))
(let (?e33 (ite $e11 ?e28 ?e29))
(let (?e34 (ite $e15 ?e29 ?e31))
(let (?e35 (ite $e21 ?e30 ?e26))
(let (?e36 (ite $e11 ?e32 ?e30))
(let (?e37 (ite $e14 ?e35 ?e34))
(let (?e38 (ite $e17 ?e7 ?e28))
(let (?e39 (ite $e19 ?e7 ?e7))
(let (?e40 (ite $e23 ?e32 v0))
(let (?e41 (ite $e12 ?e26 ?e29))
(let (?e42 (ite $e10 ?e36 ?e27))
(let (?e43 (ite $e10 v0 ?e7))
(let (?e44 (ite $e16 ?e41 ?e43))
(let (?e45 (ite $e11 ?e41 ?e43))
(let (?e46 (ite $e24 ?e33 ?e32))
(let (?e47 (ite $e17 ?e38 v0))
(let (?e48 (ite $e25 ?e27 ?e28))
(let (?e49 (ite $e20 v1 v1))
(let (?e50 (ite $e16 v1 ?e49))
(let (?e51 (ite $e12 ?e50 v1))
(let (?e52 (ite $e16 ?e51 ?e51))
(let (?e53 (ite $e19 ?e51 ?e52))
(let (?e54 (ite $e11 v1 v1))
(let (?e55 (ite $e14 ?e49 ?e50))
(let (?e56 (ite $e19 ?e52 ?e52))
(let (?e57 (ite $e14 ?e51 ?e54))
(let (?e58 (ite $e20 v1 ?e53))
(let (?e59 (ite $e15 ?e50 ?e53))
(let (?e60 (ite $e17 ?e55 ?e49))
(let (?e61 (ite $e10 ?e60 ?e50))
(let (?e62 (ite $e23 ?e57 ?e52))
(let (?e63 (ite $e23 ?e62 ?e61))
(let (?e64 (ite $e13 ?e51 ?e57))
(let (?e65 (ite $e21 ?e55 ?e63))
(let (?e66 (ite $e25 ?e51 ?e56))
(let (?e67 (ite $e24 ?e50 ?e55))
(let (?e68 (ite $e14 ?e66 ?e66))
(let (?e69 (ite $e19 ?e52 ?e67))
(let (?e70 (ite $e11 ?e53 ?e54))
(let (?e71 (ite $e18 ?e56 ?e69))
(let (?e72 (ite $e22 ?e55 ?e52))
(let (?e73 (ite $e16 v6 v5))
(let (?e74 (ite $e12 v4 v3))
(let (?e75 (ite $e25 v6 v3))
(let (?e76 (ite $e17 v5 v6))
(let (?e77 (ite $e20 ?e8 v2))
(let (?e78 (ite $e24 v5 ?e9))
(let (?e79 (ite $e23 v3 v5))
(let (?e80 (ite $e13 ?e8 ?e77))
(let (?e81 (ite $e23 v5 ?e75))
(let (?e82 (ite $e21 v4 v5))
(let (?e83 (ite $e19 v5 v5))
(let (?e84 (ite $e12 v4 ?e78))
(let (?e85 (ite $e11 ?e76 v4))
(let (?e86 (ite $e20 ?e77 ?e82))
(let (?e87 (ite $e12 v5 ?e75))
(let (?e88 (ite $e18 ?e76 ?e84))
(let (?e89 (ite $e16 ?e76 ?e75))
(let (?e90 (ite $e17 ?e77 ?e85))
(let (?e91 (ite $e17 ?e77 v4))
(let (?e92 (ite $e10 ?e91 ?e78))
(let (?e93 (ite $e18 v2 ?e73))
(let (?e94 (ite $e12 v3 ?e93))
(let (?e95 (ite $e15 ?e74 ?e73))
(let (?e96 (ite $e22 ?e95 v2))
(let (?e97 (ite $e25 v6 v5))
(let (?e98 (ite $e14 ?e97 v3))
(let (?e99 (store ?e45 ?e61 ?e74))
(let (?e100 (select ?e44 ?e60))
(let (?e101 (select ?e46 ?e57))
(let (?e102 (store ?e37 ?e67 ?e79))
(let (?e103 (select ?e33 ?e61))
(flet ($e104 (= ?e48 ?e43))
(flet ($e105 (distinct ?e40 ?e35))
(flet ($e106 (distinct ?e32 ?e44))
(flet ($e107 (distinct v0 ?e42))
(flet ($e108 (= ?e32 ?e38))
(flet ($e109 (distinct ?e41 ?e28))
(flet ($e110 (distinct ?e34 ?e31))
(flet ($e111 (= ?e26 v0))
(flet ($e112 (distinct ?e31 ?e46))
(flet ($e113 (distinct ?e48 ?e42))
(flet ($e114 (distinct ?e44 ?e29))
(flet ($e115 (distinct ?e31 ?e102))
(flet ($e116 (distinct ?e37 ?e102))
(flet ($e117 (= ?e38 ?e27))
(flet ($e118 (distinct ?e46 ?e46))
(flet ($e119 (distinct ?e26 ?e48))
(flet ($e120 (= ?e38 ?e33))
(flet ($e121 (distinct ?e31 ?e48))
(flet ($e122 (= ?e7 ?e40))
(flet ($e123 (= ?e27 ?e41))
(flet ($e124 (distinct ?e39 ?e36))
(flet ($e125 (distinct ?e36 ?e37))
(flet ($e126 (distinct ?e44 ?e41))
(flet ($e127 (= ?e40 ?e34))
(flet ($e128 (distinct ?e27 ?e43))
(flet ($e129 (distinct ?e43 ?e32))
(flet ($e130 (distinct ?e46 ?e44))
(flet ($e131 (= ?e37 ?e32))
(flet ($e132 (= ?e99 ?e43))
(flet ($e133 (distinct ?e42 ?e102))
(flet ($e134 (distinct ?e30 ?e99))
(flet ($e135 (distinct ?e27 ?e48))
(flet ($e136 (= ?e34 ?e41))
(flet ($e137 (= ?e31 ?e48))
(flet ($e138 (distinct ?e48 ?e40))
(flet ($e139 (= ?e46 ?e43))
(flet ($e140 (distinct ?e32 ?e42))
(flet ($e141 (distinct ?e42 ?e102))
(flet ($e142 (= ?e36 ?e27))
(flet ($e143 (distinct ?e28 ?e45))
(flet ($e144 (= ?e43 ?e36))
(flet ($e145 (= ?e32 ?e40))
(flet ($e146 (= ?e31 ?e28))
(flet ($e147 (distinct ?e47 ?e102))
(flet ($e148 (= ?e58 ?e71))
(flet ($e149 (distinct ?e49 ?e50))
(flet ($e150 (distinct ?e71 ?e70))
(flet ($e151 (= ?e57 ?e59))
(flet ($e152 (distinct ?e66 ?e67))
(flet ($e153 (distinct ?e56 ?e69))
(flet ($e154 (distinct ?e62 ?e57))
(flet ($e155 (distinct ?e67 ?e61))
(flet ($e156 (distinct ?e63 ?e55))
(flet ($e157 (distinct ?e63 ?e69))
(flet ($e158 (= ?e63 ?e64))
(flet ($e159 (= ?e50 ?e68))
(flet ($e160 (= ?e72 ?e63))
(flet ($e161 (distinct ?e59 ?e57))
(flet ($e162 (distinct ?e61 ?e58))
(flet ($e163 (distinct ?e53 ?e71))
(flet ($e164 (distinct ?e57 ?e66))
(flet ($e165 (= ?e60 ?e64))
(flet ($e166 (distinct ?e65 ?e54))
(flet ($e167 (distinct ?e63 ?e72))
(flet ($e168 (distinct ?e68 ?e66))
(flet ($e169 (= ?e66 v1))
(flet ($e170 (distinct ?e65 ?e59))
(flet ($e171 (= ?e61 v1))
(flet ($e172 (= v1 ?e53))
(flet ($e173 (= ?e60 ?e57))
(flet ($e174 (= ?e54 ?e49))
(flet ($e175 (distinct ?e53 ?e54))
(flet ($e176 (= ?e63 ?e70))
(flet ($e177 (distinct ?e58 ?e60))
(flet ($e178 (= ?e54 ?e59))
(flet ($e179 (distinct ?e60 ?e67))
(flet ($e180 (distinct ?e54 ?e59))
(flet ($e181 (= ?e71 ?e72))
(flet ($e182 (= ?e71 ?e66))
(flet ($e183 (= ?e66 ?e54))
(flet ($e184 (distinct ?e56 ?e66))
(flet ($e185 (distinct ?e59 ?e72))
(flet ($e186 (= ?e50 ?e50))
(flet ($e187 (= ?e55 ?e63))
(flet ($e188 (= ?e58 ?e51))
(flet ($e189 (= ?e67 ?e72))
(flet ($e190 (distinct ?e66 ?e71))
(flet ($e191 (distinct ?e66 ?e68))
(flet ($e192 (= ?e55 ?e56))
(flet ($e193 (distinct ?e49 ?e63))
(flet ($e194 (= ?e61 ?e53))
(flet ($e195 (distinct ?e57 v1))
(flet ($e196 (distinct ?e66 ?e68))
(flet ($e197 (distinct ?e60 ?e71))
(flet ($e198 (= ?e52 ?e53))
(flet ($e199 (distinct v2 v5))
(flet ($e200 (= ?e82 ?e84))
(flet ($e201 (= ?e94 ?e76))
(flet ($e202 (distinct ?e9 v6))
(flet ($e203 (= v2 ?e92))
(flet ($e204 (= ?e83 ?e88))
(flet ($e205 (= ?e79 ?e81))
(flet ($e206 (= ?e93 ?e95))
(flet ($e207 (= ?e86 ?e73))
(flet ($e208 (= ?e96 v2))
(flet ($e209 (distinct ?e84 ?e88))
(flet ($e210 (distinct ?e93 v5))
(flet ($e211 (distinct v6 ?e92))
(flet ($e212 (distinct ?e86 ?e96))
(flet ($e213 (distinct ?e8 ?e86))
(flet ($e214 (distinct v5 ?e103))
(flet ($e215 (= ?e77 ?e9))
(flet ($e216 (= ?e93 ?e75))
(flet ($e217 (= v6 ?e79))
(flet ($e218 (= v3 ?e75))
(flet ($e219 (= ?e79 ?e75))
(flet ($e220 (= ?e91 ?e92))
(flet ($e221 (distinct ?e93 ?e78))
(flet ($e222 (= ?e98 ?e77))
(flet ($e223 (= ?e76 ?e98))
(flet ($e224 (distinct ?e88 ?e94))
(flet ($e225 (distinct ?e9 ?e74))
(flet ($e226 (distinct ?e79 ?e91))
(flet ($e227 (= ?e75 v6))
(flet ($e228 (distinct ?e86 ?e90))
(flet ($e229 (distinct ?e101 ?e86))
(flet ($e230 (= ?e93 v5))
(flet ($e231 (distinct ?e84 ?e94))
(flet ($e232 (distinct v2 ?e83))
(flet ($e233 (distinct ?e85 ?e9))
(flet ($e234 (distinct ?e87 ?e81))
(flet ($e235 (distinct v5 ?e77))
(flet ($e236 (= ?e96 ?e87))
(flet ($e237 (distinct ?e87 ?e100))
(flet ($e238 (= ?e73 ?e80))
(flet ($e239 (= v4 ?e87))
(flet ($e240 (= ?e73 ?e86))
(flet ($e241 (distinct v2 ?e90))
(flet ($e242 (distinct ?e74 ?e9))
(flet ($e243 (= ?e95 ?e8))
(flet ($e244 (= v2 v6))
(flet ($e245 (= ?e97 ?e88))
(flet ($e246 (distinct ?e74 ?e73))
(flet ($e247 (distinct ?e94 ?e76))
(flet ($e248 (= ?e103 ?e85))
(flet ($e249 (= ?e84 ?e85))
(flet ($e250 (= ?e73 ?e77))
(flet ($e251 (= ?e73 v6))
(flet ($e252 (distinct v4 ?e84))
(flet ($e253 (distinct ?e98 ?e101))
(flet ($e254 (distinct ?e87 ?e81))
(flet ($e255 (= ?e94 ?e77))
(flet ($e256 (= ?e73 v5))
(flet ($e257 (distinct ?e81 ?e101))
(flet ($e258 (distinct ?e103 ?e73))
(flet ($e259 (distinct ?e92 ?e89))
(flet ($e260 (and $e120 $e210))
(flet ($e261 (and $e127 $e173))
(flet ($e262 (iff $e174 $e249))
(flet ($e263 (if_then_else $e114 $e240 $e185))
(flet ($e264 (implies $e198 $e156))
(flet ($e265 (or $e203 $e263))
(flet ($e266 (and $e255 $e204))
(flet ($e267 (implies $e243 $e209))
(flet ($e268 (if_then_else $e222 $e112 $e199))
(flet ($e269 (or $e145 $e257))
(flet ($e270 (if_then_else $e10 $e134 $e136))
(flet ($e271 (or $e264 $e131))
(flet ($e272 (iff $e218 $e226))
(flet ($e273 (xor $e152 $e195))
(flet ($e274 (xor $e262 $e13))
(flet ($e275 (if_then_else $e177 $e108 $e12))
(flet ($e276 (not $e247))
(flet ($e277 (implies $e180 $e275))
(flet ($e278 (not $e196))
(flet ($e279 (and $e242 $e151))
(flet ($e280 (xor $e273 $e148))
(flet ($e281 (or $e212 $e235))
(flet ($e282 (if_then_else $e172 $e201 $e25))
(flet ($e283 (not $e14))
(flet ($e284 (if_then_else $e267 $e168 $e146))
(flet ($e285 (and $e219 $e16))
(flet ($e286 (xor $e272 $e105))
(flet ($e287 (xor $e21 $e141))
(flet ($e288 (xor $e160 $e266))
(flet ($e289 (xor $e208 $e245))
(flet ($e290 (or $e116 $e135))
(flet ($e291 (xor $e202 $e225))
(flet ($e292 (iff $e133 $e268))
(flet ($e293 (xor $e179 $e278))
(flet ($e294 (iff $e110 $e287))
(flet ($e295 (not $e241))
(flet ($e296 (and $e163 $e106))
(flet ($e297 (xor $e265 $e122))
(flet ($e298 (not $e295))
(flet ($e299 (iff $e164 $e290))
(flet ($e300 (and $e244 $e143))
(flet ($e301 (xor $e238 $e189))
(flet ($e302 (if_then_else $e15 $e284 $e260))
(flet ($e303 (or $e259 $e297))
(flet ($e304 (and $e197 $e190))
(flet ($e305 (iff $e250 $e296))
(flet ($e306 (implies $e153 $e118))
(flet ($e307 (or $e288 $e270))
(flet ($e308 (if_then_else $e298 $e221 $e253))
(flet ($e309 (if_then_else $e111 $e23 $e170))
(flet ($e310 (implies $e159 $e228))
(flet ($e311 (not $e138))
(flet ($e312 (or $e167 $e11))
(flet ($e313 (xor $e279 $e289))
(flet ($e314 (xor $e206 $e227))
(flet ($e315 (or $e312 $e157))
(flet ($e316 (xor $e261 $e313))
(flet ($e317 (implies $e314 $e183))
(flet ($e318 (or $e317 $e165))
(flet ($e319 (implies $e22 $e175))
(flet ($e320 (if_then_else $e213 $e293 $e293))
(flet ($e321 (iff $e280 $e299))
(flet ($e322 (not $e169))
(flet ($e323 (or $e234 $e117))
(flet ($e324 (not $e150))
(flet ($e325 (if_then_else $e223 $e258 $e184))
(flet ($e326 (xor $e237 $e178))
(flet ($e327 (or $e307 $e19))
(flet ($e328 (if_then_else $e303 $e192 $e274))
(flet ($e329 (xor $e230 $e316))
(flet ($e330 (implies $e239 $e24))
(flet ($e331 (and $e324 $e154))
(flet ($e332 (implies $e246 $e132))
(flet ($e333 (implies $e121 $e128))
(flet ($e334 (xor $e181 $e107))
(flet ($e335 (xor $e322 $e321))
(flet ($e336 (iff $e200 $e139))
(flet ($e337 (and $e325 $e147))
(flet ($e338 (iff $e220 $e166))
(flet ($e339 (implies $e276 $e326))
(flet ($e340 (if_then_else $e20 $e104 $e254))
(flet ($e341 (not $e292))
(flet ($e342 (implies $e306 $e335))
(flet ($e343 (implies $e294 $e229))
(flet ($e344 (or $e328 $e186))
(flet ($e345 (if_then_else $e162 $e333 $e256))
(flet ($e346 (iff $e125 $e217))
(flet ($e347 (and $e345 $e336))
(flet ($e348 (or $e271 $e251))
(flet ($e349 (implies $e144 $e342))
(flet ($e350 (if_then_else $e302 $e308 $e302))
(flet ($e351 (xor $e182 $e347))
(flet ($e352 (if_then_else $e18 $e188 $e343))
(flet ($e353 (iff $e126 $e349))
(flet ($e354 (or $e233 $e320))
(flet ($e355 (implies $e215 $e341))
(flet ($e356 (not $e211))
(flet ($e357 (not $e344))
(flet ($e358 (or $e334 $e309))
(flet ($e359 (or $e315 $e337))
(flet ($e360 (if_then_else $e277 $e155 $e283))
(flet ($e361 (not $e339))
(flet ($e362 (not $e232))
(flet ($e363 (or $e123 $e142))
(flet ($e364 (not $e363))
(flet ($e365 (not $e353))
(flet ($e366 (and $e124 $e231))
(flet ($e367 (not $e161))
(flet ($e368 (or $e364 $e137))
(flet ($e369 (iff $e367 $e109))
(flet ($e370 (xor $e360 $e310))
(flet ($e371 (not $e362))
(flet ($e372 (and $e357 $e331))
(flet ($e373 (and $e252 $e207))
(flet ($e374 (if_then_else $e140 $e140 $e115))
(flet ($e375 (or $e291 $e214))
(flet ($e376 (not $e351))
(flet ($e377 (iff $e311 $e236))
(flet ($e378 (if_then_else $e372 $e248 $e361))
(flet ($e379 (xor $e374 $e350))
(flet ($e380 (and $e216 $e370))
(flet ($e381 (implies $e301 $e224))
(flet ($e382 (iff $e379 $e130))
(flet ($e383 (iff $e158 $e354))
(flet ($e384 (not $e346))
(flet ($e385 (or $e171 $e338))
(flet ($e386 (xor $e191 $e378))
(flet ($e387 (iff $e282 $e330))
(flet ($e388 (and $e281 $e281))
(flet ($e389 (implies $e387 $e318))
(flet ($e390 (implies $e176 $e359))
(flet ($e391 (and $e358 $e366))
(flet ($e392 (implies $e365 $e371))
(flet ($e393 (and $e383 $e340))
(flet ($e394 (or $e390 $e369))
(flet ($e395 (not $e389))
(flet ($e396 (not $e323))
(flet ($e397 (and $e394 $e193))
(flet ($e398 (implies $e391 $e368))
(flet ($e399 (iff $e395 $e398))
(flet ($e400 (and $e392 $e129))
(flet ($e401 (or $e17 $e399))
(flet ($e402 (implies $e396 $e396))
(flet ($e403 (iff $e401 $e386))
(flet ($e404 (implies $e376 $e319))
(flet ($e405 (if_then_else $e269 $e205 $e194))
(flet ($e406 (and $e380 $e332))
(flet ($e407 (xor $e402 $e403))
(flet ($e408 (if_then_else $e329 $e113 $e382))
(flet ($e409 (and $e286 $e187))
(flet ($e410 (implies $e393 $e300))
(flet ($e411 (implies $e388 $e355))
(flet ($e412 (implies $e409 $e352))
(flet ($e413 (implies $e397 $e405))
(flet ($e414 (xor $e373 $e400))
(flet ($e415 (not $e285))
(flet ($e416 (not $e119))
(flet ($e417 (not $e305))
(flet ($e418 (xor $e348 $e408))
(flet ($e419 (if_then_else $e149 $e304 $e415))
(flet ($e420 (if_then_else $e407 $e377 $e419))
(flet ($e421 (xor $e381 $e385))
(flet ($e422 (not $e420))
(flet ($e423 (iff $e422 $e411))
(flet ($e424 (or $e375 $e404))
(flet ($e425 (xor $e414 $e384))
(flet ($e426 (implies $e327 $e406))
(flet ($e427 (implies $e424 $e412))
(flet ($e428 (implies $e421 $e417))
(flet ($e429 (and $e427 $e413))
(flet ($e430 (or $e410 $e356))
(flet ($e431 (if_then_else $e429 $e425 $e418))
(flet ($e432 (xor $e430 $e430))
(flet ($e433 (iff $e431 $e426))
(flet ($e434 (and $e432 $e423))
(flet ($e435 (xor $e434 $e428))
(flet ($e436 (xor $e433 $e433))
(flet ($e437 (and $e416 $e435))
(flet ($e438 (implies $e437 $e436))
$e438
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

