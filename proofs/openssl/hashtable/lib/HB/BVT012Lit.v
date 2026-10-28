(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
From Corelib Require Import PrimString.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietCodec.  (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require StrLz HBLzD.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition t012_ (_ : unit) : acs := dec_acs (StrLz.lz_decd HBLzD.d "'#1>>50@$5/<1#-@#(>.@62>+;>'=8?;06@+$<(@#?>.3>@$'>.8/&$451@#)@+$>4@#<@,6'+4@*#,5&=40=5@,6',&<40=@#&@+$?4$2=@0@@%9@5#?062@9@%9@5$>;5101@@@@%9@5@:'@%9@5@&(@)>>=&:2<8@-%@%9@5$?90==0;#20#/0=:+'(1>>5:81$#0>3+$)55934!#131/@$0@$717%<40@#(>2*>@.0@$717&>>2>@&7@%9@5$9>0?,>?#10#/0?.%&@&%@%9@5#=03:8@$5@%9@533<+7=8>@63<+@@+@%9@5%>>1@#(>59*@%-=87<-##55278!##69?0?14,@#$@%9@541926<>57192@'6@$6(=@++@%9@5@#11$2@.9@%9@5@#106@'5@$4?#@)/@%9@5@#106@'5@$4.(@()@%9@58.8@'1@$3;?@(2@%9@5@#&@+$'931.(7=),$800@5)@%9@59@+$'942$;@#'1)54@$218@#41)5<$5@#31)55@$25)@#,1)54$.@#(1(.<$)@,,@%9@5&:275@#,@%9@571'.@,9@%9@58-=@,2@%9@5&=8?;5>3/-@&(@$//;56+>@$-@$//;22&38=2),61'*@8*@%9@5&=97=7>?<30=2%.&=96>3=.&-@%#@$/*6$=6@#*@$/*6710,@-#@%9@5&=8?;22%-#<5=+=%@%-@$.?.12$2819;@#(@$.>+71%5@02@%9@5%?:3@'/@%9@511:3@#%@$.3(71)>@0#@%9@57197@#%@$.&51@$.#+@#/6-6@2$@%9@581'-@#$@$-3-@#(@$-/(81'+@)7@$-/(@&*@$-,?%;?91?$@(%==;0=*%1$?90?>8&4:@*#?1@&+/+&;?900@%9@5%:274=+9*&:2753=,@7$9?1>=<<4('1#9#45=/8@&9?244=/8@&9?243=+5&$9>1@#/$)4$@#>1@#/';6%6%>46@%>@%9@5120/$1<@#16=4@-&@%9@5$9>0?8;82=+5%&9>44@$-@%9@5%9>42=*99@#($31$.@#&?'82@(&@%9@501,)@#-@$-#-61,.@/$@$-#-$9>0@%%1+*!##723<>3@%9@5%:123='/'$=80=27803><2#@3=/)3$:10?0'<21&@21'4@%%@$,>&11)+#:51@17=/%871)%@+2@%9@5&:1:83=(&9#:1@#0;?:=.>%&:2774=.>%&:12=3=.>%&:12=3=/$/#31?8$98=.;<#31?7:732790#7#62@$%(892$.1#@22672#12=.16#31?6<1==.0(#31?6;>6#5$153=0#'$9?1>@?0<=.$'&9?2:6=.#$&9?2:2=.#$$9?1@%289<=-@,$9?1=,<)@%4@%9@501-=#6781-@#%4(2@++@$+4=$731?(+$21$>&:277@'4=-;7#=0@$&)5&6:270@#>@>(##;?8?@#%@%9@5%?924=-08$=80=6.?';=8?>26(@0?#@1'=97;0@@(@%9@5)69000#60?'+913@,2=**003*&0=*--0476127>02/%0$)027$2289%12>429(#10>,,:219&2=*,?01?)1=1*3#21?/'&225<$153=**9$?90>.,'419?3=$8,0=>15(1!##770?49#1*-1@$':3#80?46:3#71@$':3-#-;4888,8-60606?;0606072@$%?@#70@#1@1@#&@$&#$#70@#1@$@#*$$@#,%&7@$'.@:@$&%(#70@#1>9@#)%&8@$&(.@#,@%9@2-#)730=8#4528!##5>44@#(@%9@3$=40=.=01#/0>=4:#21#/0?/4@0#/2>8>)02(-$083@$%)(%=8?41#+#:3?&16@#%=&&2@@@@)>>;@@6@)>>;$9>0119#21#/1>@%$0#/1@#*#%2@%9;2$9>0?>3)6#40?*=:1#.1@#);(5#@1?.8'1#4$7312$)23(90=@.<8@+$'7#70?7.%:@%9>,#81?70,0@+$'7%=416=>/86@%9>.%=41@#&?-#>7@%9>.$?:@#'?(8,@@@@)>?1@=1@)>?1#8@#%@#<47@*$@)>?1%=46@#$@#9@$@@@@+$'7@@@@+$'7@@@@+$'7@@@@+$'7@9%@+$'7(>1=50%0:'-#81:1<-#(%#69>3=0#69>418%0<;:#81:5#-#/%#733540#7335:0%#73392017=6*%#78?:340#)+8%#7?21200#)-#04%#8031=8#8031>0%#806:<40#)-#%8%#848=88#8480@.$16-#,78178#8793?8%#88?<440#)-#%8%#8:0=8<#8:00$1';<0;00#)-#08%#8;??28#8;??30%#90?6600#)+4%#9221500#)0@'681%=<00#)+8%#988<?00#)-#04%#9;64>8#9;64?0%#:26?000#)+4%#:45?880#)+<%#:8>3800#)-#84%#:=>468#:=>470%#;3>::8#;3>:;0%08'##81:3%#%0#*0#1+>0%#;=8?=0=2@6%>0%0<)>0=%.%%08%1=%.-1=%/1-#&%#;?9130#;?9230#1-#4660#;?9?08%#879400#8794>4,46@0+@(:9$0@#+<2@@@@%9;>@5)@%9;>$>;@'&@%9;>%;202@%9;>"%pstring).
Abbreviation t012 := (t012_ tt).

Definition t012_sig_a0e_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 514)) (ELit 8192)));
  (1118%nat, (ELit 0));
  (1119%nat, (ELit 0))].
Abbreviation t012_sig_a0e := (t012_sig_a0e_ tt).
Definition t012_sig_a2e_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 514)) (ELit 8192)));
  (1118%nat, (ELit 0));
  (1119%nat, (ELit 1))].
Abbreviation t012_sig_a2e := (t012_sig_a2e_ tt).
Definition t012_sig_a1e_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 514)) (ELit 8192)));
  (1118%nat, (ELit 0));
  (1119%nat, (ELit 0))].
Abbreviation t012_sig_a1e := (t012_sig_a1e_ tt).
Definition t012_sig_b0e_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EMd M_MUL (ELit 4096) (EVar 5)));
  (1118%nat, (ELit 4096));
  (1119%nat, (ELit 0))].
Abbreviation t012_sig_b0e := (t012_sig_b0e_ tt).
Definition t012_sig_b2e_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EMd M_MUL (ELit 4096) (EVar 5)));
  (1118%nat, (ELit 4096));
  (1119%nat, (ELit 1))].
Abbreviation t012_sig_b2e := (t012_sig_b2e_ tt).
Definition t012_sig_b1e_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EMd M_MUL (ELit 4096) (EVar 5)));
  (1118%nat, (ELit 4096));
  (1119%nat, (ELit 0))].
Abbreviation t012_sig_b1e := (t012_sig_b1e_ tt).
Definition t012_sig_a0o_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 514)) (ELit 8192)));
  (1118%nat, (ELit 0));
  (1119%nat, (ELit 0))].
Abbreviation t012_sig_a0o := (t012_sig_a0o_ tt).
Definition t012_sig_a1o_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 514)) (ELit 8192)));
  (1118%nat, (ELit 0));
  (1119%nat, (ELit 0))].
Abbreviation t012_sig_a1o := (t012_sig_a1o_ tt).
Definition t012_sig_b0o_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EMd M_MUL (ELit 4096) (EVar 5)));
  (1118%nat, (ELit 4096));
  (1119%nat, (ELit 0))].
Abbreviation t012_sig_b0o := (t012_sig_b0o_ tt).
Definition t012_sig_b1o_ (_ : unit) : list (nat * expr) :=
 [(1117%nat, (EMd M_MUL (ELit 4096) (EVar 5)));
  (1118%nat, (ELit 4096));
  (1119%nat, (ELit 0))].
Abbreviation t012_sig_b1o := (t012_sig_b1o_ tt).
Definition t012_F_a0e_ (_ : unit) : list kentry := [(KAlign (EVar 6) 2)].
Abbreviation t012_F_a0e := (t012_F_a0e_ tt).
Definition vhpl_a0e_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 0; ELit 5] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 0) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (EVar 514) 1 34359736318) (PFact (KRange (ELit 0) 0 1) (PHandoff 950)))))).
Abbreviation vhpl_a0e := (vhpl_a0e_ tt).
Definition t012_F_a2e_ (_ : unit) : list kentry := [(KAlign (EVar 6) 2)].
Abbreviation t012_F_a2e := (t012_F_a2e_ tt).
Definition vhpl_a2e_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 6; ELit 6] (PExt 49 [ELit 187; EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 549)) (ELit (-8)); ELit 10176] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 0) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (EVar 514) 1 34359736318) (PFact (KRange (ELit 1) 0 1) (PHandoff 952))))))).
Abbreviation vhpl_a2e := (vhpl_a2e_ tt).
Definition t012_F_a1e_ (_ : unit) : list kentry := [(KAlign (EVar 6) 2)].
Abbreviation t012_F_a1e := (t012_F_a1e_ tt).
Definition vhpl_a1e_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 11; ELit 255] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 0) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (EVar 514) 1 34359736318) (PFact (KRange (ELit 0) 0 1) (PHandoff 953)))))).
Abbreviation vhpl_a1e := (vhpl_a1e_ tt).
Definition t012_F_b0e_ (_ : unit) : list kentry := [(KAlign (EVar 6) 2)].
Abbreviation t012_F_b0e := (t012_F_b0e_ tt).
Definition vhpl_b0e_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 0; ELit 5] (PExt 47 [ELit 42; ELit 41] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 4096) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (ELit 0) 0 1) (PHandoff 955)))))).
Abbreviation vhpl_b0e := (vhpl_b0e_ tt).
Definition t012_F_b2e_ (_ : unit) : list kentry := [(KAlign (EVar 6) 2)].
Abbreviation t012_F_b2e := (t012_F_b2e_ tt).
Definition vhpl_b2e_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 6; ELit 6] (PExt 49 [ELit 187; EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 549)) (ELit (-8)); ELit 10176] (PExt 47 [ELit 42; ELit 41] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 4096) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (ELit 1) 0 1) (PHandoff 957))))))).
Abbreviation vhpl_b2e := (vhpl_b2e_ tt).
Definition t012_F_b1e_ (_ : unit) : list kentry := [(KAlign (EVar 6) 2)].
Abbreviation t012_F_b1e := (t012_F_b1e_ tt).
Definition vhpl_b1e_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 11; ELit 255] (PExt 47 [ELit 42; ELit 41] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 4096) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (ELit 0) 0 1) (PHandoff 958)))))).
Abbreviation vhpl_b1e := (vhpl_b1e_ tt).
Definition t012_F_a0o_ (_ : unit) : list kentry := [(KAlign (EAlu ALU_ADD (EVar 6) (ELit 1)) 2)].
Abbreviation t012_F_a0o := (t012_F_a0o_ tt).
Definition vhpl_a0o_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 0; ELit 5] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 0) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (EVar 514) 1 34359736318) (PFact (KRange (ELit 0) 0 1) (PHandoff 951)))))).
Abbreviation vhpl_a0o := (vhpl_a0o_ tt).
Definition t012_F_a1o_ (_ : unit) : list kentry := [(KAlign (EAlu ALU_ADD (EVar 6) (ELit 1)) 2)].
Abbreviation t012_F_a1o := (t012_F_a1o_ tt).
Definition vhpl_a1o_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 11; ELit 255] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 0) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (EVar 514) 1 34359736318) (PFact (KRange (ELit 0) 0 1) (PHandoff 954)))))).
Abbreviation vhpl_a1o := (vhpl_a1o_ tt).
Definition t012_F_b0o_ (_ : unit) : list kentry := [(KAlign (EAlu ALU_ADD (EVar 6) (ELit 1)) 2)].
Abbreviation t012_F_b0o := (t012_F_b0o_ tt).
Definition vhpl_b0o_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 0; ELit 5] (PExt 47 [ELit 42; ELit 41] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 4096) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (ELit 0) 0 1) (PHandoff 956)))))).
Abbreviation vhpl_b0o := (vhpl_b0o_ tt).
Definition t012_F_b1o_ (_ : unit) : list kentry := [(KAlign (EAlu ALU_ADD (EVar 6) (ELit 1)) 2)].
Abbreviation t012_F_b1o := (t012_F_b1o_ tt).
Definition vhpl_b1o_ (_ : unit) : plan := PExt 38 [EVar 6; ELit 11; ELit 255] (PExt 47 [ELit 42; ELit 41] (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 433))) (ELit 4096)) 0 4192) (PFact (KRange (ELit 4096) 0 4096) (PFact (KRange (EVar 433) 0 1) (PFact (KRange (ELit 0) 0 1) (PHandoff 959)))))).
Abbreviation vhpl_b1o := (vhpl_b1o_ tt).
#[global] Opaque t012_.   (* [comment removed for export] *)
