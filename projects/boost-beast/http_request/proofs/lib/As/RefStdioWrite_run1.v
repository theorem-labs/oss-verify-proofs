(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import RefStdioDefs As_code_104cb0_104f8c .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_sub_Z : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.

Lemma v_add_Z : forall a (l : word), (0 <= a < 2^64)%Z ->
  v_add (Z_to_bv 64 a) l = Z_to_bv 64 (a + bv_unsigned l).
Proof. intros a l H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_wZ : forall (b : word) c, (0 <= c < 2^64)%Z ->
  v_add b (Z_to_bv 64 c) = Z_to_bv 64 (bv_unsigned b + c).
Proof. intros b c H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_ZZ' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. u_norm. reflexivity. Qed.

Lemma sltu0_xor_ne : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> a <> b ->
  v_sltu (Z_to_bv 64 0) (v_xor (Z_to_bv 64 a) (Z_to_bv 64 b)) = Z_to_bv 64 1.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.lxor); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.Z_lxor_range); constr:(@Stdlib.ZArith.BinInt.Z.ltb_spec); constr:(@Corelib.Init.Datatypes.BoolSpec); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.False_ind); constr:(@Stdlib.ZArith.BinInt.Z.lxor_eq); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.StepTac.u_Z2bv); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.v_sltu); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.v_xor)|] [|@z; @Hlt; @Ha; @__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @__sat0; @__sat1; @Hge; @b; @b1; @b0; @Hr; @Hne; @Hb; @a|] "#%O#0#k#3#6#W###X#V#$#&#'#E#*#%#(#)#^#0#;#\#H#+#I#M#P#]#`#e#i#8#<#@#?#F#G#L#N#O#Q#R#S#U#[#_#a#b#c#f#g#d#/#.#K#,#J#j#k#m#l#5#7#=#D#C#:#B#A#Z#Y#4#T#h#>#93#\%#]%#^&#_%#`%#a$#b%#c%#d'#e*#&&#f%#g+#h&#i)#j$#DI(S#2#($(#(#(#(#2#VS.)#$I#.-#%CJNUS/#US0)US1#'$D)%#'&K)'#&F#')#)*#*(#2S#'-#nL#$##-%#%###,%.#$j#$C#&OF'2#)3#*1#nL#$##4##%#*#3%5#+j#$C#&OK'9#):#*F#nL#$##;##%#1#:%<#2j#$C#XS2KJNI&KJ#D#$$s#'.$#*DFnL#$##s#$##%#:#s##%s#%#;j#$C#VS3D2$D3#4D*D5WS%%$#&PO*D#&MP$D##$DnL#$##s#1I#%#s#'#s#0%s#2#s#(&S&M$D#VS's#5s#+j#%$#U#F#'D%s#9s#8s#/VS4s#Gs#A$Ds#H#Ds#C$Ds#Ck##$#k##&##Ds#MWS5s#Ns#HIj##S(#j#&%##Ds#Jk##S(#k#&(#US6S)US7S)VS8CIUS9CUS:CVS;CS#VS*CD+C$S$#,&HEEG#QUS<E+C&S$',)HEEG#QZS=*HEEGJ[S++HEEG$#+C+S>*,-HEEG#Q/.HEEG%)#//HEEG+*#VS?0GVS'LS,VS@FN%L#S,m$%#WSACDIXSBFN$#l#'*)#l#(:9#l#)=<#j#*C#j#+R##FD.s#uN%CNDk##$#k##&#k#*C#k#+R#&SCSD$#s#sXF#$JMl#,-&#l#-s#/s#,#l#.s#9s#4#WSESFS&#UO#VSGs#=#j#/s#?#U#FnS%%s#Js#I%#0##s#GI#%$##s#B$###l#1s#ML#l#2s#Ts#P#/s#1HEEGs#(s#,s#*l#'#s#$>l#(s#5s#4#l#)s#8s#7#j#*C#j#+R##DF.#Ik###s$5k#*C#k#+R#$s#Ts$/-#s#UJl#,*%#l#-s#Gs#D#l#.s#Qs#L#VS*Cs$;WSHC#s$0+Cs#BS-#,s#DHEEG#Q[S+s#EHEEGs#=#/s#FHEEG#s#A$l#'#s#9s#3l#(s#Js#I#l#)s#Ms#L#j#*C#j#+R#$Fs$?.I#k###s$@k#*C#k#+R##Ds#i-#s#jJl#,*%#l#-s#\s#Y#l#.s#fs#a#0s$.8#1Cs$/s#|s#)s$-#l#3s$)s$%#USIC+Cs#XS$s#X,s#[HEEG#Ql#'#s#Ns#Hl#(&s#^#l#)s#bs#a##DDl#,$#F+Cs#_S-A,s#bHEEG#Ql#'#s#Us#Ol#(-s#e#l#)s#is#h#l#,#s#tFl#-s#os#l#l#.s#ys#t#0D+#1CDs$<4s$U#'s$YJ)s$Z#$Ps$`-#PKl#,s#;s#6#l#-s#xs#u#l#.s$&s#}##DP-#PKl#,s#+s#&#l#-s#}s#z#l#.s$+s$&#0J(#1CJs$Q0.#$Ms$l-#MOl#,s#Gs#B#l#-s$(s$%#l#.s$2s$-##DM-#MOl#,s#7s#2#l#-s$-s$*#l#.s$7s$2#0K(#1CKs$d.s$m#VSJs$o<VSKs$r#%s$t#s$jm#&#j#4s$x#j#5s${#j#&s$|#j#0C#j#6C##"). Qed.

Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof.
  intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
  rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

Lemma sltu_ge : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.

Lemma sltu_lt : forall a b, (0 <= a < b)%Z -> (b < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.

Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
  intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
  destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.

Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.

Lemma v_and_m1_l : forall a, (0 <= a < 2^64)%Z ->
  v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 a) = Z_to_bv 64 a.
Proof.
  intros a H. unfold v_and. u_norm.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  f_equal. apply Z.mod_small. lia.
Qed.

Lemma v_subw_small_lit : forall a b, (0 <= b <= a)%Z -> (a < 2^31)%Z ->
  v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b H H2. unfold v_subw. u_norm.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw1 (mem : word -> option byte) (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (can : word) (wb n : Z) (s l : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (su - 8))  (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (su - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 (su - 24)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (su - 32)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (su - 40)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 (su - 48)) (word_to_le_bytes 8 s4))
    (Z_to_bv 64 (su - 56)) (word_to_le_bytes 8 s5))
    (Z_to_bv 64 (su - 64)) (word_to_le_bytes 8 s6))
    (Z_to_bv 64 (su - 72)) (word_to_le_bytes 8 can))
    (Z_to_bv 64 (su - 104)) (word_to_le_bytes 8 (Z_to_bv 64 wb)))
    (Z_to_bv 64 (su - 96)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (Z_to_bv 64 (su - 88)) (word_to_le_bytes 8 s))
    (Z_to_bv 64 (su - 80)) (word_to_le_bytes 8 l).
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.RefStdioDefs.sw_file Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma sw_enter : forall regs mem rom (su f wb wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x11fc30 <= f)%Z -> (f + 232 <= 0x11fe10)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wb < wp)%Z -> (wp < 2^64)%Z -> (wp - wb + bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x104dfc : word) mem rom)
      (mkst regs' (0x104e84 : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 104)
    /\ getr regs' 12 = Z_to_bv 64 2
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 (su - 104)
    /\ getr regs' 21 = Z_to_bv 64 0x67d4f0
    /\ getr regs' 22 = Z_to_bv 64 (wp - wb + bv_unsigned l)
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom su f wb wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WBP WPhi SMALL.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_104dfc D_104dfc. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_104e00 D_104e00 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_104e04 D_104e04 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_104e08 D_104e08 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_104e0c D_104e0c (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_104e10 D_104e10 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_104e14 D_104e14 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_104e18 D_104e18 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_104e1c D_104e1c (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_104e20 D_104e20. rewrite Ha2.
    stepn F_104e24 D_104e24. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_104e28 D_104e28.
    stepLD8 F_104e2c D_104e2c (Z_to_bv 64 0x67d4f0).
    stepLD8 F_104e30 D_104e30 can.
    stepST F_104e34 D_104e34 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepLD8 F_104e38 D_104e38 (Z_to_bv 64 wp).
    stepLD8 F_104e3c D_104e3c (Z_to_bv 64 wb).
    (* [comment removed for export] *)
    stepn F_104e40 D_104e40. rewrite (v_sub_Z wp wb) by lia.
    stepn F_104e44 D_104e44.
    (* [comment removed for export] *)
    stepST F_104e48 D_104e48 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
    stepST F_104e4c D_104e4c (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
    stepST F_104e50 D_104e50 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_104e54 D_104e54 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_104e58 D_104e58. rewrite (v_add_Z (wp - wb) l) by lia.
    stepn F_104e5c D_104e5c. rewrite (sltu0_xor_ne wp wb) by lia.
    (* [comment removed for export] *)
    stepb_ft F_104e60 D_104e60 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_104e64 D_104e64.
    replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepn F_104e68 D_104e68.
    (* [comment removed for export] *)
    stepLD F_104e70 D_104e70 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_104e74 D_104e74.
    stepn F_104e78 D_104e78.
    stepn F_104e7c D_104e7c.
    stepn F_104e80 D_104e80.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_enter_eq : forall regs mem rom (su f wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x11fc30 <= f)%Z -> (f + 232 <= 0x11fe10)%Z ->
  sw_file mem f wp wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wp < 2^64)%Z -> (bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x104dfc : word) mem rom)
      (mkst regs' (0x104e84 : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wp 0 s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 88)
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 (su - 88)
    /\ getr regs' 21 = Z_to_bv 64 0x67d4f0
    /\ getr regs' 22 = l
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom su f wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WPhi SMALL.
  pose proof (u64_range l) as Hl.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_104dfc D_104dfc. rewrite Hsp. sp_renorm.
    stepST F_104e00 D_104e00 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_104e04 D_104e04 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_104e08 D_104e08 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_104e0c D_104e0c (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_104e10 D_104e10 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_104e14 D_104e14 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_104e18 D_104e18 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_104e1c D_104e1c (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    stepn F_104e20 D_104e20. rewrite Ha2.
    stepn F_104e24 D_104e24. rewrite Ha0.
    stepn F_104e28 D_104e28.
    stepLD8 F_104e2c D_104e2c (Z_to_bv 64 0x67d4f0).
    stepLD8 F_104e30 D_104e30 can.
    stepST F_104e34 D_104e34 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    stepLD8 F_104e38 D_104e38 (Z_to_bv 64 wp).
    stepLD8 F_104e3c D_104e3c (Z_to_bv 64 wp).
    stepn F_104e40 D_104e40. rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
    stepn F_104e44 D_104e44.
    stepST F_104e48 D_104e48 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
    stepST F_104e4c D_104e4c (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
    stepST F_104e50 D_104e50 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_104e54 D_104e54 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    stepn F_104e58 D_104e58.
    stepn F_104e5c D_104e5c. rewrite sltu0_xor_eq.
    (* [comment removed for export] *)
    stepb_tk F_104e60 D_104e60 ltac:(apply c_eq_refl).
    stepn F_104e6c D_104e6c.
    replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepLD F_104e70 D_104e70 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_104e74 D_104e74.
    stepn F_104e78 D_104e78.
    stepn F_104e7c D_104e7c.
    stepn F_104e80 D_104e80.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
