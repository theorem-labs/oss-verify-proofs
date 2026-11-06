(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
From Corelib Require Import PrimString.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import DietCodec.  (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require StrLz HALzD.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition t012_ (_ : unit) : acs := dec_acs (StrLz.lz_decd HALzD.d "'#1?363>+;>$36@#(>+;>7@(>%1$706@+$<(@#?>.3>@$'>.8/&$451@#)@+$>4@#<@,6'+7@*#,5#98@,6',#9@#&@+$?4$2<@0@@%9@516<<9@%9@5#;6=(%<@@@@%9@5@:'@%9@5@&+@)>>=#4@-%@%9@5$<61=/460#/1=::*%?360@';>>$<60=/9,&51<>2@#4&4#4@#->.:/@#3@$7170>8@%?$(@.3@$717#7@&9@%9@52>*+=0=9#$0?#2,@&$@%9@5#7@$;@%9@533<+7=8>@63<+@@-@%9@5@#)>4/.@%/=87<$752@%9@5#?@#(@%9@541926<>57192@'6@$6(=@++@%9@5@#11$2@.9@%9@5@#106@'5@$4?#@)/@%9@5@#106@'5@$4.(@()@%9@58.8@'1@$3;?@(2@%9@5@#&@+$'931.(7=),$800@5)@%9@59@+$'942$;@#'1)54@$218@#41)5<$5@#31)55@$25)@#,1)54$.@#(1(.<$)@,.@%9@5$;1@#,@%9@571'.@,9@%9@58-=@,5@%9@5#75>3/-@&(@$//;56+>@$-@$//;22&38=2),61'*@8-@%9@58>?<34=2%.3=.&-@%#@$/*6#7@#+@$/*6710,@-&@%9@52='6*$385=+=%@%-@$.?.12$2819;@#(@$.>+71%5@02@%9@5#<0@#<154,06$*@&3@%9@511:3@#%@$.3(71)>@0#@%9@57197@#%@$.&51@$.#+@#/6-6@2$@%9@581'-@#$@$-3-@#(@$-/(81'+@)7@$-/(@&*@$-,?%;<61@#1>.%>2<3;#+1?-=42:@*$<60=:%?';<63=1=1,3#;1=8='1#/6=/8@7?'325=+227=/8@$606=/8@$607@$-+?;=/8@2??';5#6#85>.,%@%4@$-(6120/$1<@#16=4@-(@%9@51@#.+%4#2#0@$/@%9@5@#'@&1>*;=/,>@#&?&;3@(&@%9@501,)@#-@$-#-61,.@/&@$-#-$815=/*?#:6@%9@5#:6=/)30?9>'$771@%;4(%>6:5=/)30?*+<21&@21'4@%%@$,>&11)+#:51@17=/%871)%@+5@%9@50>+0>125,0?4,58=.3?&66?;0=/742=.>%#96=.>%#96=/$/2>)2941>%3=.4?32795=.3$@#'=.7822676=.2@1=.-,1=(*@>=.0(1@#$(;6@%9@5#=5@%9@51@#$#<>=.$'#69=.#$0@&7(;3=.&/@#%=-@,0=*7)@%4@%9@501-=#6781-@#%4(2@+/@$+4=1@#$$(38*%0=01@@'/=-;7#758/:2@%9@5&<63;@#$@%9@5%<666><)10?<:+0=-/.2=-/72698$70@@/@%9@5#94=*--0>+=;6>;747=/8'42/%3=*,?#96=*,?#:6=*,?4=*/$#?0>*7=41?)4=*,?2=/*=223>2=*(=%<630@&8#+319?4@$':33@$$:5&740=569?3@$':3#=6@-&&&5@%9@5@##@$&#'@%1@$&&-5$$@#+@$&%+#25@$'*/?@%9@50>*?$@#7@%9@5(50#44;0=//1$;=2@$&8'11).52=.%;:16=*7:#10=1,=2@$%,=0?/@;5@$%+%4@$%)+#87@$%)+31#.$77@#&?'17@@@@)>>>@@@@)>>>0?*391#/3@$'-7%66;1@#4#(6@%9=;1@#*.+5@%9<;4>*$81@$)>&7#@2@#*(.447:1>-+503(<0=>,%:@+$':#=0=9/8:@%9>/0?14/3@+$':#<@#'@%9>1@#&?)077@%9>1#<0@$'2+@#&6>?@@@@)>?4@=/@)>?4@#$?.2>@*&@)>?46>2/8=$+@@@@+$':@@@@+$':@@@@+$':@@@@+$':@8?@+$':#91@$3:8#80=5?&0=54&%;790=5>51=565%;281:5&)%#700900=52&#61@%9@2$>017=6*%#7798400#)+8%#7:?5000#)+8%#81<5500#)+8%#8774:00#)+8%#886:;00#)+8%#8=65800#)-#&8%#8=9088#8=900@.$29-$1:;28#8>:;30%#8?6::8#8?6:;0%#91<>>8#91<>?0%#923768#923770@.$,*-#*4=8#93>4>0%#9688000#)-#08%#9<=018#9<=020%#:3<8200#)+8%#:533:00#)+8%#:8:?;00#)-#%8%#:>=<58#:>=0@$3$8-#,28;78#;29880%#;32>>00#)1=55&0@'6/%#61@$3&8#60@$3&81@$3+8$630=5'5&3:0%0<*#0=%.($<80#1#=0#1#>0#@+4?0#;<65?0#1-#%:20#;<72<8,46@0,@(:86#>@@@@%9;2@5-@%9;2#;@''@%9;2$783@%9;2"%pstring).
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
