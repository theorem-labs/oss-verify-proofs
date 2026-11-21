(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame Hoare.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import LazyRestrict LazySR.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import RefExitBase RefStdioDefs.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsLazyRun.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsStdioWrite.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SC_KEPT : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Record stdio_res : Type := SCR_ {
  sc_f : Z;            (* [comment removed for export] *)
  sc_fd : Z;           (* [comment removed for export] *)
  sc_ret : Z;          (* [comment removed for export] *)
  sc_wb : expr;        (* [comment removed for export] *)
  sc_wp : expr;        (* [comment removed for export] *)
  sc_bufp : expr;      (* [comment removed for export] *)
  sc_bufsz : expr;     (* [comment removed for export] *)
  sc_s : expr;         (* [comment removed for export] *)
  sc_l : expr;         (* [comment removed for export] *)
  sc_sp : expr;        (* [comment removed for export] *)
  sc_sr : list expr;   (* [comment removed for export] *)
  sc_kn : list kentry  (* [comment removed for export] *)
}.

Definition lit_even_ret (e : expr) : option Z :=
  match e with
  | ELit r => if ((r mod 2 =? 0) && (0 <=? r) && (r <? two64))%bool then Some r else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
      else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
  | _ => [K]
  end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.

Definition stdio_call (nv : nat) (sr : list expr) (kn : list kentry) : option stdio_res :=
  match nth 10 sr (ELit 0), lit_even_ret (nth 1 sr (ELit 0)) with
  | ELit f, Some ret =>
    match kread RSEGS kn (ELit 0) (f + 120) 4, kread RSEGS kn (ELit 0) (f + 40) 8, kread RSEGS kn (ELit 0) (f + 56) 8,
          kread RSEGS kn (ELit 0) (f + 88) 8, kread RSEGS kn (ELit 0) (f + 96) 8,
          kread RSEGS kn (ELit 0) 0x1203f0 8, kread RSEGS kn (ELit 0) 0x681830 8 with
    | Some (ELit fd), Some wp, Some wb, Some bufp, Some bufsz, Some (ELit cg), Some _ =>
      let sp := nth 2 sr (ELit 0) in
      let '(qb, k0) := split_lit sp in
      let qk := (k0 - 112)%Z in
      match kindex (is_kwr_cov qb qk 112) kn 0, base_range kn qb with
      | Some _, Some (blo, bhi) =>
        if ((0x123ef0 <=? f) && (f + 232 <=? 0x1240d0)
            && ((fd =? 1) || (fd =? 2)) && (cg mod two64 =? 0x681830)
            && (4294967296 + 112 <=? blo + k0) && (bhi + k0 <=? 0x800000000000)
            && expr_vars_lt nv bufp && expr_vars_lt nv bufsz
            && sr_vars_lt nv sr && kn_vars_lt nv kn && Nat.eqb (length sr) 32)%bool
        then
          let k0 := kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8 in
          let k1 := kn_frame k0 qb qk 112 in
          let k2 := kn_frame k1 (ELit 0) (f + 32) 16 in
          let k3 := kn_frame k2 (ELit 0) (f + 56) 8 in
          Some (SCR_ f fd ret wb wp bufp bufsz (nth 11 sr (ELit 0)) (nth 12 sr (ELit 0)) sp
                     (sr_upd (sr_after_call_j sr SC_KEPT nv) 10 (nth 12 sr (ELit 0)))
                     (KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
                      :: KWord (SA (ELit 0) (f + 40)) 8 bufp
                      :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3))
        else None
      | _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.

Lemma inr_spec : forall lo n x, inr lo n x = true <-> (lo <= bv_unsigned x < lo + n)%Z.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Corelib.Classes.Morphisms_Prop.and_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.and_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStdioCall.inr)|] [|@lemma; @B; @H1; @H0; @H; @x; @n; @lo|] "##p#)#J#)#1###%#3#9#&#$#<#5#7#4#B#A#:#'#(#I#,#0#.#-#?#@#C#D#E#G#F#H#J#K#2#/#6#8#>#=#;,#C&#D$#1%#E%#F%#$%#G%#H%#I,$S&$#$#$#$#$#US'#US(#&$EVLF#'FJVM%#VN%##G#H#G'H#G&H%$#(&#&.JVLI#'IFVM%#VN%##G#H#G'H#G&H%$#*I+),*%$#VS)C#+CDK*'E$$#j#$1#VS*:8*F<(7#%+-WS+CDS,XOCD#/ZP1.E00#+CDK0&#--,j#$(#VS-Fs#$)s#%s##(?#k#%CCXS.CCDDXOCD,6_S/C%D$QP7#96E+CDK/6#665j#$(#VS0s#-s#+%4+k###:&s#2F'RI)$#&s#5I*S##'S#R)%#XS$%#JEj#&(#j#'s#&#YS1s#'s#&s#%#Ej#(/#XS$//##V32#V=<#Vs#'s#&#WS2FJE#G#H(#6m#&#j#)s#E#j#*S%#j#+S%##"). Qed.

Lemma inr_false : forall lo n x, inr lo n x = false <-> ~ (lo <= bv_unsigned x < lo + n)%Z.
Proof. intros lo n x. rewrite <- inr_spec. destruct (inr lo n x); split; congruence. Qed.

(* [comment removed for export] *)
Lemma know_ok_frame3 : forall E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3,
  know_ok RSEGS E M kn ->
  flat E (SA b1 o1) n1 -> flat E (SA b2 o2) n2 -> flat E (SA b3 o3) n3 ->
  (forall x : word,
     ~ (estart E (SA b1 o1) <= bv_unsigned x < estart E (SA b1 o1) + n1)%Z ->
     ~ (estart E (SA b2 o2) <= bv_unsigned x < estart E (SA b2 o2) + n2)%Z ->
     ~ (estart E (SA b3 o3) <= bv_unsigned x < estart E (SA b3 o3) + n3)%Z ->
     M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 o1 n1) b2 o2 n2) b3 o3 n3).
Proof.
  intros E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3 HK F1 F2 F3 Hout Hg.
  set (a1 := estart E (SA b1 o1)) in *. set (a2 := estart E (SA b2 o2)) in *. set (a3 := estart E (SA b3 o3)) in *.
  set (M1 := fun x : word => if (inr a2 n2 x || inr a3 n3 x)%bool then M x else M' x).
  set (M2 := fun x : word => if inr a3 n3 x then M x else M' x).
  assert (O1 : forall x : word, (bv_unsigned x < a1 \/ a1 + n1 <= bv_unsigned x)%Z -> M1 x = M x).
  { intros x Hx. unfold M1. destruct (inr a2 n2 x) eqn:E2; [reflexivity|]. destruct (inr a3 n3 x) eqn:E3; [reflexivity|].
    cbn [orb]. apply inr_false in E2. apply inr_false in E3. apply Hout; [lia | exact E2 | exact E3]. }
  assert (G1 : mem_grows M M1).
  { intros x Hx. unfold M1. destruct (inr a2 n2 x || inr a3 n3 x)%bool; [exact Hx | exact (Hg x Hx)]. }
  assert (O2 : forall x : word, (bv_unsigned x < a2 \/ a2 + n2 <= bv_unsigned x)%Z -> M2 x = M1 x).
  { intros x Hx. unfold M1, M2. destruct (inr a3 n3 x) eqn:E3; [rewrite orb_true_r; reflexivity|].
    destruct (inr a2 n2 x) eqn:E2; [|reflexivity]. apply inr_spec in E2. lia. }
  assert (G2 : mem_grows M1 M2).
  { intros x Hx. unfold M1, M2 in *. destruct (inr a3 n3 x); [rewrite orb_true_r in Hx; exact Hx|].
    destruct (inr a2 n2 x); cbn [orb] in Hx; [exact (Hg x Hx) | exact Hx]. }
  assert (O3 : forall x : word, (bv_unsigned x < a3 \/ a3 + n3 <= bv_unsigned x)%Z -> M' x = M2 x).
  { intros x Hx. unfold M2. destruct (inr a3 n3 x) eqn:E3; [|reflexivity]. apply inr_spec in E3. lia. }
  assert (G3 : mem_grows M2 M').
  { intros x Hx. unfold M2 in Hx. destruct (inr a3 n3 x); [exact (Hg x Hx) | exact Hx]. }
  eapply know_ok_frame; [| exact F3 | exact O3 | exact G3].
  eapply know_ok_frame; [| exact F2 | exact O2 | exact G2].
  eapply know_ok_frame; [exact HK | exact F1 | exact O1 | exact G1].
Qed.

Lemma Forall_one' : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof. intros A P x H. constructor; [exact H | constructor]. Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | |lo hi| | | |]; cbn [kimg_cut1]; try (apply Forall_one'; exact HKK).
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_one'; exact HKK|].
  apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Himg).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_one'. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
  - destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_one'. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
Qed.

Lemma u_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros E. cbn [edenot]. apply u64_lit. lia. Qed.

Lemma flat_abs0 : forall E off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z ->
  flat E (SA (ELit 0) off) n.
Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite u_lit0. lia. Qed.
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr Sort Prop.
Scheme kc__2 := Elimination for LinuxProcessSemantics.Riscv.Instr.aluop Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.env); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.split_lit); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.edenot); constr:(@stdpp.bitvector.definitions.bv); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Logic.eq_sym); constr:(@stdpp.bitvector.definitions.Z_to_bv_bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add_0_r); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@LinuxProcessSemantics.Riscv.Instr.aluop); constr:(@Corelib.Init.Logic.f_equal); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.BinInt.Z.add_0_l); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.AgentLib.u64_lit); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EVar); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EAlu); constr:(@kc__2); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.v_add); constr:(@Corelib.Numbers.BinNums.N); constr:(@kc__3); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.add_mod_idemp_r); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.bv_wrap64_mod); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@LinuxProcessSemantics.Riscv.Sem.alu64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.alu_add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EAluw); constr:(@LinuxProcessSemantics.Riscv.Instr.mulop); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EMd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EMdw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EExt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EBlob); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SUB); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SLL); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SLT); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SLTU); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_XOR); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SRL); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SRA); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_OR); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_AND)|] [|@z; @e'; @b0; @n; @op0; @a; @b1; @sx; @lo; @e0; @k; @i; @op; @e; @b; @H; @p; @Ha; @__ff; @__varmap; @__wit; @__arith; @__sat1; @__sat0; @H0; @b2; @__sat3; @__sat2; @e2_2; @e2_1; @e2; @k0; @e1; @G; @E|] "#1)#?$A#C#D###T#$#%#($'#)#&#'#*#0#1#/#+$##2#8#.#,#4#5#X#-#6#o#z#7#3$7$<$=$>$?$@$A$B$C$D#p#n#9#<#:#F#u#>#_#`#c#h#s#{#~$)#V#G#M#K#R#Q#U#\#^#b#d#f#e#g#i#j#k#m#t#w#v#l#x#|#}#y#]$($+$*$0$/$1$.$4$5#;$&#B#E$%#H#Y#Z#J#S#N#P#I$,$-$$$6$8$9$:$;#L#O#[#a#W#r#q$2$3A$&&$'&$('$))$*)$+%$,%$-%$.%$/)#1$$0%$1%$2$$3&$4&$5&$6'$7'$8$$9$$:%$;%#<$$<$$='$>*$?$$@%#6$VS@CDUSLH%CDGE#%$#6SM6#6#6#6#6#USN#*IE($#7%*KG+'E#%$#j#$D#+*(VSO+*XSP)$+#)+FUSQ,,D-(%$#j#%C#+1&#/1#k#%C#;F%CD#E%CDGF%CDHE%CDMF%CDKF%CDNFnC#$#&s#%E#+$#$&$#'%&#(#)#*$&#(#)#*$&#(#)#*$&#(#)#*$'#+#,#'#-#'#+#.#/#'#%CDLFnS*#$#0s#'H#-#$##################nC#$#1s#(E#+$#$+$#'*&#0#2#&#&#0#)#2$&#0#)#2$&#0#)#2$'#+#,#'#-('#+#.#/#'(%CDML#s#*$#*NG*NI(s###)#M+s#%##s##'#k#3)#j#1C#%CDIM#s#47#nS@%CD$#4DE#$%#1#$Ej#1s#6#%CD;G%CDKI&s#9D%$#E#DGInS@%CD$#4CE#$%#1#$Gj#1s#<#%CDAH%CDNK&s#?C%$#G#Cs#$N#Cs#%R#DIS';K*O#*OG(s#<#)#S++s#>##s#<'#k##*#j#2C##DMR*Os#1(s#D#)#E+s#F##s#D/#j#.D#+s#IK)EK+s#K##s#I%#j#$D##s#K's#Ij#$D#+s#PI8s#N#)FIUSRI,DI'%$#+s#UF(s#V#USCs#]USCs#YVSS$#VSDF%9F%VST'&VSDF#k##%#k##'#9F+WSU,+Gj##SE#j#5%#9F*k##SE#k#5(#VSVF28SW#m##1UG#USXSFUSYSFUSZDUS[DUS\DVSGDF<D#S]#=%S<S-S-S;#SAVSGD>WS^D#s#t<D'S_#=)S<S-S-S;#SA[S`*S<S-S-S;'#VSa+S;8S.SHVSbEH#S.#SHm$%#WScDFGXSdEH$#l#6*)#l#754#l#887#9FFVSI#s#(l#9%#El#:=s#)#l#;s#%B#l#:s#0s#*#VSeF#,DFs#>s#7s#5#;I*Q#*Qs#z(s$1#)#I+s$3##s$1'#m#*#'DIs#L#S'Ej#3s#S#'Cs$&s#U#S'Ej#3s#`#U#El#<s#ds#c#U#El#<s#ls#k#j#3s#r#j#$D#U#Ej#$D#0E%CD#F#s$N#s#y0G%CD#F&s$QDs#y#s#wE#DFI0H%CD#F&s$UCs#w#s#uG#C%N0L#C#R0M#DFS'0K*O##s$P#s#sk##&#j#2C##DFR(s$W')#E+s$Y##s$W*#j#.D#0IUN#'DF%#S'Ej#3+#'C3-#S'Ej#35#U#El#<:9#U#El#<@?#j#3s#$#j#'S##U#Ej#'S##$LHG%CD#F$IML%CD#F$KIM%CD#FnC#$#&s$zE#+$#$s$[$#''&#(#)#*%&#(#)#*%&#(#)#*%&#(#)#*%'#+#,#'#-#'#+#.#/#'#$HGE%CD#FnS*#$#0s$}H#-#%##################%CDS'R#s%#$#%CDME$GML%CD#F$LKI%CD#F$MNK%CD#FnC#$#&s%+H#+$#$)$#''&#(#)#*%&#(#)#*%&#(#)#*%&#(#)#*%'#+#,#'#-#'#+#.#/#'#$ELH%CD#FnS*#$#0s%.E#-#%##################%CDS&S+#s%0$#*P.*PQ(s%)#)#S&+s%+##s%)'#k#3)#j#)S*#%CDLE$JLH%CD#F$JIM%CD#F$JKI%CD#FnC#$#&s%@G#+$#$)$#''&#(#)#*%&#(#)#*%&#(#)#*%&#(#)#*%'#+#,#'#-#'#+#.#/#'#%CDS+S'#s%B$#%CDIE$JIG%CD#F$JNL%CD#F$JRM%CD#FnC#$#&s%JE#+$#$)$#''&#(#)#*%&#(#)#*%&#(#)#*%&#(#)#*%'#+#,#'#-#'#+#.#/#'#%CDQS&#s%L$#*S$+*S$O(s%E#)#Q+s%G##s%E'#k#3)#j#1C#%CDOQ#s%V5#%CDKG%CDPO&s%YDs%%$#E#DGO%CDNH%CDS$P&s%]Cs%#$#G#CNS$#CRS0#DIS($JS&s$|*S%#*S%G(s%Z#)#S)+s%\##s%Z'#k##*#j#2C##DMS0*S%S&(s%b#)#E+s%d##s%b/#j#.D#*S/S+VSf#s$v))K+s%j##s%hE#j#2s%i#7E7G7H##GE(LH(LG#D$#k##&#(HG(HE#D$#7L##HGk##%#VSI)#7M##LHk##-#j##&#j##$Ej##/#WSgHGEYSh1+&$#j#=8#j#*:#j#'SJ#k#=;/k#*=#k#'SJ#(s&.s%C)s#+#+s&0#.s&1$*S=Q(s&3#)#N+s&5#(s&6##DE#j#$D#.s&9K))E.s&;##D#(j#$D#.s&>s#3.s&?N)/#.s&A##D#Ej#$D#)s#@-/#s%G.s&F4#DE#j#$D#/Ks%K/2s%L#D#'j#$D#/s#Bs%O/Ns%P)>#/#s%R#D#Ej#$D#/As%U#DE#j#$D#8D+)s#S0/#s%Z<Ds%CSis%G=s%IS<S-S-S;#SAZSjs%JS<S-S-S;#l#6#s%Bs%<l#7s%Ns%M#l#8s%Qs%P##Ds%aFk###Skl#9%#El#>s%Vs%b#l#?s%^s%[#l#>s%is%c#XSls#aKs%g#,D;320#>s#\,D=8$s#,#>K,Ds##@$s#3#.s&ks#)>s#*,Ds#*s#'%$#(s&ns#b?s&os#d,Ds#4s#/%$#?s&qK,Ds#;s#7$s#F#(s&ss#E?s&ts#G,Ds#Fs#?%$#XEs&vs#Hs#j#l#3s#Os#L#(s&xs#o)#I+s&z##s&xs#q#m#'#WSmJs#ts&/VSns#us&0,s&|s#us#q%$#$JS+s%T*S/##s'##*m#&#'DIs#|#S(Ej#3s$'#'CS's$)#S(Ej#3s$4#U#El#<s$8s$7#U#El#<s$>s$=#j#3s$B#j#$D#U#Ej#$D#$JIs%P%CD#F#s'@#s$I$JKs%P%CD#F&s'CDs&k#s$IE#DFO$JNs%P%CD#F&s'GCs&i#s$IG#C%S$$JRs%P#C#S0$JS's%P#DFS($JS&s%P*S%##s'B#s$Gk##&#j#2C##DFS0(s'I')#E+s'K##s'I*#j#.D#$JS+s%PUS$#'DF%#S(Ej#3+#'C3-#S(Ej#35#U#El#<:9#U#El#<@?#j#3s#$#j#'S##U#Ej#'S##$JS's%I%CD#F%CDS(S0#s'i$#$JS+s%T%CD#F%CDS)S(&s'mDs'9$#E$MLH$JS&#%CD#F%CDS,S)&s'rCs'8$#G#C&S,$JQs%\#C#S/$JOs%\#DFS%$RNK$JS$#*S>#*S>G(s'r#)#S=+s't##s'r'#k##+#j#2C##DFS/(s'y+)#E+s'{##s'y.#j#.D#$NKI$JP#:#'DF&#S%Ej#3,#'C9.#S%Ej#3;#U#El#<@?#U#El#<s#'s#H#j#3s#,#j#@C#j#AC#j#0S*#W#HGEj#2C#j#)C#j#0S*#1HGE$JS'#%CD#F#s(B#s#81LHG$JS+#%CD#F&s(FDs'n#s#8E1MLH$JS&#%CD#F&s(JCs'l#s#7G#C%S,1IML$JQ##C#S/1KIM$JO#1RNK$JS$#*S>##s(G#s#4k##s#<#j#2C#(s(M&)#E+s(O##s(M)#j#.D#1NKI$JP#:#'DF&#S%Ej#3s#<#'C3-#S%Ej#36#U#El#<<;#U#El#<Bs#x#j#3s#'#j#@C#j#AC#j#0S*#W#HGEj#2C#j#)C#j#0S*#2HGE$JS'#%CD#F#s(r#s#h2LHG$JS+#%CD#F&s(vDs(B#s#hE2MLH$JS&#%CD#F&s(zCs(@#s#gG#C%S,2IML$JQ##C#S/2KIM$JO#2RNK$JS$#*S>##s(w#s#dk##s#l#j#2C#(s(}&)#E+s)###s(})#j#.D#2NKI$JP#:#'DF&#S%Ej#3s#l#'C3-#S%Ej#36#U#El#<<;#U#El#<Bs$L#j#3s#'#j#@C#j#AC#j#0S1#W#HGEj#2C#j#)C#j#0S1#3HGE$JS'#%CD#F#s)F#s$<3LHG$JS+#%CD#F&s)JDs(r#s$<E3MLH$JS&#%CD#F&s)NCs(p#s$;G#C%S,3IML$JQ##C#S/3KIM$JO#3RNK$JS$#*S>##s)K#s$8k##s$@#j#2C#(s)Q&)#E+s)S##s)Q)#j#.D#3NKI$JP#:#'DF&#S%Ej#3s$@#'C3-#S%Ej#36#U#El#<<;#U#El#<Bs$|#j#3s#'#j#@C#j#AC#j#0S1#W#HGEj#2C#j#)C#j#0S1#4LHGE$JS&#%CD#F#s)v#s$c4MLHG$JQ#%CD#F%CDS/S,&s){Ds)G$#E#DFS,4IMLH$JO#%CD#F%CDS%S/&s*%Cs)G$#G#C&S%4KIML$JP##C#S=4NKIM$JS$##DFS?4S'RNK$JS(#*SB#*SBG(s*'#)#So+s*)##s*''#k##+#j#2C##DFS=(s*.+)#E+s*0##s*..#j#.D#4RNKI$JS0#US%#'DF&#S?Ej#3,#'C9.#S?Ej#3<#U#El#<BA#U#El#<s#*s#)#j#3s#0#j#BC#j#'S##j#,S##j#+S.#X#LHGEj#1C#j#'S##j#,S##j#+S.#5LHGE$JS&#%CD#F#s*U#s%B5MLHG$JQ#%CD#F&s*YDs*%#s#=E5IMLH$JO#%CD#F&s*]Cs*##s#;G#C%S%5KIML$JP##C#S=5NKIM$JS$#5S'RNK$JS(#*SB##s*Z#s#6k##s#>#j#2C#(s*`&)#E+s*b##s*`)#j#.D#5RNKI$JS0#US%#'DF&#S?Ej#3s#>#'C3-#S?Ej#36#U#El#<<;#U#El#<Bs#[#j#3s#'#j#'S##j#/D#j#CS##j#+S.#X#LHGEj#'S##j#/D#j#.S##j#+S.#^SKs(2s&Is%}s%Hs$ts$Ds#ps#5#HU#Ej#3s(F#$S2HG%CD#F#s+-#s(J$S2LH%CD#F&s+0Ds*X#s(_E#DFS+$S2ML%CD#F&s+4Cs*V#s(GG#C%Q$S2IM#C#O$S2KI#DFP$S2RN*S)#*S)G(s+3#)#S$+s+5##s+3'#k##*#j#2C#(s+9*)#E+s+;##s+9-#j#.D#$S2NK-#'DF%#PEj#3s&e#'C6,#PEj#38#U#El#<=<#U#El#<s##B#j#3s#'#$S3HG%CD#F#s+U#s(r$S3LH%CD#F&s+XDs+$#s)+E$S3ML%CD#F&s+[Cs*}#s(nG#C%Q$S3IM#C#O$S3KI$S3RN*S)##s+U#s#%k##s#,#j#2C#(s+[&)#E+s+]##s+[)#j#.D#$S3NK-#'DF%#PEj#3s'+#'C1,#PEj#33#U#El#<87#U#El#<=s#D#j#3A#$S4HG%CD#F#s+w#s)8$S4LH%CD#F&s+zDs+F#s)ME$S4ML%CD#F&s+}Cs+C#s)4G#C%Q$S4IM#C#O$S4KI$S4RN*S)##s+w#s#Gk##s#N#j#2C#(s+}&)#E+s,###s+})#j#.D#$S4NK-#'DF%#PEj#3s'M#'C1,#PEj#33#U#El#<87#U#El#<=s#f#j#3A#$S5HG%CD#F#s,=#s)Z$S5LH%CD#F&s,@Ds+h#s)oE$S5ML%CD#F&s,CCs+e#s)VG#C%Q$S5IM#C#O$S5KI$S5RN*S)##s,=#s#ik##s#p#j#2C#(s,C&)#E+s,E##s,C)#j#.D#$S5NK-#'DF%#PEj#3s'o#'C1,#PEj#33#U#El#<87#U#El#<=s$,#j#3A#$S6HG%CD#F#s,_#s)|$S6LH%CD#F&s,bDs,.#s*5E$S6ML%CD#F&s,eCs,+#s)xG#C%Q$S6IM#C#O$S6KI$S6RN*S)##s,_#s$/k##s$6#j#2C#(s,e&)#E+s,g##s,e)#j#.D#$S6NK-#'DF%#PEj#3s(5#'C1,#PEj#33#U#El#<87#U#El#<=s$N#j#3A#$S7HG%CD#F#s-%#s*B$S7LH%CD#F&s-(Ds,P#s*WE$S7ML%CD#F&s-+Cs,M#s*>G#C%Q$S7IM#C#O$S7KI$S7RN*S)##s-%#s$Qk##s$X#j#2C#(s-+&)#E+s--##s-+)#j#.D#$S7NK-#'DF%#PEj#3s(W#'C1,#PEj#33#U#El#<87#U#El#<=s$p#j#3A#$S8HG%CD#F#s-G#s*d$S8LH%CD#F&s-JDs,r#s*yE$S8ML%CD#F&s-MCs,o#s*`G#C%Q$S8IM#C#O$S8KI$S8RN*S)##s-G#s$sk##s$z#j#2C#(s-M&)#E+s-O##s-M)#j#.D#$S8NK-#'DF%#PEj#3s(y#'C1,#PEj#33#U#El#<87#U#El#<=s%6#j#3A#$S9HG%CD#F#s-i#s+*$S9LH%CD#F&s-lDs-8#s+?E$S9ML%CD#F&s-oCs-5#s+&G#C%Q$S9IM#C#O$S9KI$S9RN*S)##s-i#s%9k##s%@#j#2C#(s-o&)#E+s-q##s-o)#j#.D#$S9NK-#'DF%#PEj#3s)?#'C1,#PEj#33#U#El#<87#U#El#<=s%X#j#3A#$S:HG%CD#F#s./#s+L$S:LH%CD#F&s.2Ds-Z#s+aE$S:ML%CD#F&s.5Cs-W#s+HG#C%Q$S:IM#C#O$S:KI$S:RN*S)##s./#s%[k##s%b#j#2C#(s.5&)#E+s.7##s.5)#j#.D#$S:NK-#'DF%#PEj#3s)a#'C1,#PEj#33#U#El#<87#U#El#<=s%z#j#3A#`Sps+us&'s%[s%9s$ss$Qs$/s#is#Gs#%#LU#Ej#3s,0#j#BC#j#DC#j#0S*#W#HGEj#2C#j#)C#j#0S*#%CDs(xF#s.Z#s,:%CDs(vF&s.\Ds.(#s+yE%CDs(tF&s.^Cs.$#s,1G#Cs(vS&#Cs(rQ*S(s(n*S(G(s.Y#)#P+s.[##s.Y'#k##s*%#j#2C##DFQ(s.`+)#E+s.b##s.`.#j#.D#@s(q'DF$#OEj#3*#'Cs)%,#OEj#35#U#El#<98#U#El#<=s,{#j#3@#j#BC#j#DC#j#0S*#W#HGEj#2C#j#)C#j#0S*#%CDs(oF#s/%#s,a%CDs(mF&s/'Ds.O#s,DE%CDs(kF&s/)Cs.K#s,XG#Cs(mS&#Cs(iQ*S(s(e#s.|#s#&k##s*H#j#2C#(s/&&)#E+s/(##s/&)#j#.D#@s(c'DF$#OEj#3s#,#'Cs(s+#OEj#30#U#El#<43#U#El#<8s-A#j#3;#j#BC#j#DC#j#0S1#W#HGEj#2C#j#)C#j#0S1#%CDs(aF#s/G#s-'%CDs(_F&s/IDs.q#s,fE%CDs(]F&s/KCs.m#s,zG#Cs(_S&#Cs([Q*S(s(W#s/B#s#Hk##s*j#j#2C#(s/H&)#E+s/J##s/H)#j#.D#@s(U'DF$#OEj#3s#N#'Cs(e+#OEj#30#U#El#<43#U#El#<8s-c#j#3;#j#BC#j#DC#j#0S1#W#HGEj#2C#j#)C#j#0S1#%CDs(SF#s/i#s-<j#-s/js/7%CDs(RF&s/lD$#s-#E#DFS&j#-s/ns/5%CDs(PF&s/pC$#s,yG#Cs(RO#Cs(MP#DFS$*S,s(I*S,G(s/l#)#S0+s/n##s/l'#k##)#j#2C#(s/r*)#E+s/t##s/r-#j#.D#UOs(F'DF$#S$Ej#3s'L#'Cs(\+#S$Ej#35#U#El#<98#U#El#<?>#j#3s###j#1C#j#'S##j#,S##j#+S.#X#LHGEj#1C#j#'S##j#,S##j#+S.#%CDs(DF#s09#s-h%CDs(BF&s0;Ds/c#s-NE%CDs(@F&s0=Cs/_#s-FG#Cs(BO#Cs(>P*S,s(:#s04#s#'k##s#-#j#2C#(s0:&)#E+s0<##s0:)#j#.D#UOs(8'DF$#S$Ej#3s'p#'Cs(H+#S$Ej#30#U#El#<43#U#El#<8s#B#j#3;#j#'S##j#/D#j#CS##j#+S.#X#LHGEj#'S##j#/D#j#.S##j#+S.#^SKs0,s.os.Gs$bs$;s#us#Ss#'#MU#Gl#Es0Fs0C#j#3s0\#j#.D#j#2C#j#1C#j#FSq##"). Qed.

Lemma split_lit_vars : forall n e b k, split_lit e = (b, k) -> expr_vars_lt n e = true -> expr_vars_lt n b = true.
Proof.
  intros n e b k H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [reflexivity | exact Hv]).
  lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

Lemma kindex_some : forall p kn i j, kindex p kn i = Some j ->
  exists K, nth_error kn (j - i) = Some K /\ p K = true /\ (i <= j)%nat.
Proof.
  intros p kn. induction kn as [|K rest IH]; intros i j H; cbn [kindex] in H; [discriminate|].
  destruct (p K) eqn:HP.
  - injection H as <-. exists K. rewrite Nat.sub_diag. cbn. auto.
  - destruct (IH (S i) j H) as (K' & Hn & HP' & Hle). exists K'.
    replace (j - i)%nat with (S (j - S i))%nat by lia. cbn [nth_error]. repeat split; try assumption. lia.
Qed.

Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sr_get_nat : forall sr n, (0 < n < 32)%nat -> sr_get sr (Z_to_bv 5 (Z.of_nat n)) = nth n sr (ELit 0).
Proof.
  intros sr n Hn. unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_lit by lia. reflexivity.
Qed.
Scheme kc__4 := Elimination for Corelib.Init.Datatypes.nat Sort Prop.

Lemma length_sr_upd : forall sr n e, (n < length sr)%nat -> length (sr_upd sr n e) = length sr.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.expr); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Peano.lt); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.sr_upd); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.cons); constr:(@kc__4); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Numbers.BinNums.xO)|] [|@e; @n; @sr; @y; @x; @__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @cstr1; @cstr0; @cstr; @Hn0; @Hn; @__x2; @IH; @t; @h|] "#%F#/#k#<#3#5#$#Q###%#E#=#'#R#P#&#*#)#C#6#D#(#Y#Z#8#F#\#f#2#:#B#I#L#J#U#`#a#/#;#+#j#k#l#@#?#K#M#O#X#V#[#]#^#b#c#_#i#,#m#.#g#e#4#7#A#9#H#G#>#T#S#d#h#W#N4#_%#+$#8&#3%#`%#a&#;$#4%#b%#c$#d/#e'#f*#g&#h%#i%#j+US,D#DI&F#(OIF#D##DO%E$#k##'#k#$D#k#%E#j#&,#US-D#D#&F#(%IF#D#%E#&$$$(%C$#US(EUS(C$F$H%C$#%EFHVS;FHWS<%$#j#'E#j#(E#'C/'C/-EC.K-%31$60#&IR$I*#J'C$'CJ-ECS#KS$S)I&$RJ#XS.(&#H,>+J9,L$L+J#(s#$S%L#D#,#$$+J#US-S/US,S/US=CVS0CFXS1C$F#US>CUS?CVS2CJUS@S&2C#.C%SA#/'NGGM#S'USBG.C&S*(/*NGGM#S'ZSC+NGGMO3,NGGM$&#3-NGGM('#VSD.M'S3S4VSEHI%S3#S4m$%#WSFCJFXSGHI$#l#)*)#l#*87#l#+=<#j#,C#j#-S5#+JH*FJk###Ok##%#k#,C#k#-S5#(s#MPQ#D#$#%C#s#I$PXH$#ILl#./)#l#/s#0s#.#l#0s#6s#4#l#1s#9s#8#l#2s#;s#?#XS6s#Ss#Ps#C#j#3s#W#j#$D#j#%E#0DLO#D#&F##DS%)#&H#0DPQ(#FO#D##D%%E$#k#3(#j#%E##DL)#&R#'E.0DQS%(#RI#D##D%%E$#m#(#j#3*#)H#DQ)#&%##DP#DS7)#%E)#j#%E#)''E#(PFL#D#&F+$,*s#x#'Cs#y'C%-ECS#KS$S)Fs#{$0&#)F&#-USHS&1s$##1+$*$#1H&j#(C#U#s$(`S8EECCS+KK$S9Fs$).U%1`S8EECCS+KK&S9<2/-ECS#KS$S).&%8$#XS..*#H,I+Js$##DSI,#$$+J#VS0CIXS1C#Fs#s2CS&VS2C7WS:C$#USJS&2C#WS:C#&.C&S*#/s#wNGGM#S'.C*S*&/s#yNGGM#S'3s#zNGGM%s#t#l#)#s#os#il#*/s#}#l#+s$'s$&#j#,C#j#4C#1Fs#&*s###*FIk##$#k#,C#k#4C##DSK$#$S%WH$#Ol#.-'#l#0B@#l#1s#&s#%#l#2s#(s#0#XS6s#<s#:s#7#WQFL#ZSLEs#Gs#Cs#As#?#0DS7P(#s#:L#D##D%%E$#m#(#j#3s#O#j#%E#U#Hj#%E#XSMs#bs#W#IU#Hj#3s#n#j#$D#j#%E#j#5s$s#j#6s$}#j#7D#YSNDs$us#w#Hj#&s%$##"). Qed.

Lemma nth_sr_upd_same : forall sr n e, (n < length sr)%nat -> nth n (sr_upd sr n e) (ELit 0) = e.
Proof.
  intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
  destruct n; cbn [sr_upd nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_sr_upd_other : forall sr n m e, n <> m -> nth m (sr_upd sr n e) (ELit 0) = nth m sr (ELit 0).
Proof.
  intros sr. induction sr as [|h t IH]; intros n m e Hne.
  - revert m Hne. induction n as [|n IHn]; intros m Hne; cbn [sr_upd].
    + destruct m; [lia | destruct m; reflexivity].
    + destruct m; [reflexivity|]. cbn [nth]. rewrite IHn by lia. destruct m; reflexivity.
  - destruct n; destruct m; cbn [sr_upd nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.

Lemma length_sr_after_call_j : forall sr kept nv, length (sr_after_call_j sr kept nv) = 32%nat.
Proof. intros. unfold sr_after_call_j. rewrite length_map, length_seq. reflexivity. Qed.
Scheme kc__5 := Elimination for Corelib.Init.Datatypes.option Sort Prop.
Scheme kc__6 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__7 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.
Scheme kc__8 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__9 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.kentry Sort Prop.
Scheme kc__10 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.saddr Sort Prop.
Scheme kc__11 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__12 := Elimination for Corelib.Init.Logic.False Sort Prop.
Scheme kc__13 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.
Scheme kc__14 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Bo.RefStdioDefs.sw_post Sort Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem stdio_call_sound :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z ->
  (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds mo) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  (* LPS 75d69e00: the reader premise, next to the fd_lookup one -- as As/AsStdioCall.v. *)
  m_channel_reader mo = true ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x109138) M (seg_rom RSEGS) ->
  K [] ->
  (forall R' M' msF' mo',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS) ->
     realizes RSEGS (mkCfg msF' mo') K) ->
  realizes RSEGS (mkCfg msF mo)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  (* LPS 75d69e00: was a KReplay replay of as_stdio_write, one argument short of the reader
     premise; written out.  Same text as As/AsStdioCall.v's stdio_call_sound (donor
     boost-json As/AsStdioCall.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6), re-keyed to this image by THIS tree's own
     As/Bo pair of [stdio_call] bodies: entry 0x104dfc -> 0x109138, guard cell
     0x11c130 -> 0x1203f0, canary 0x67d4f0 -> 0x681830, FILE bounds 0x11fc30/0x11fe10 ->
     0x123ef0/0x1240d0. *)
  intros vals ebs sr kn R M L S Zr msF mo res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0x1203f0 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x681830 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwphi Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr OK RS HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x1203f0 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x681830 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x109138) with (0x109138%bv : word) in RS by (apply bv_eq; reflexivity).
  eapply (as_stdio_write R M L S Zr msF mo su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hrdr.
  - exact OK.
  - exact RS.
  - lia.
  - lia.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' msF' mo' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST OK' SB' HS' RS'.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply (HCONT R' M' msF' mo'); [ | | exact OK' | exact SB' | exact HS' | exact RS'].
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [(first [clear - Hfd12; lia | lia])|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. (first [clear - Hfd12 Hretv Hq N1; lia | lia]).
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
Qed.

(* [comment removed for export] *)
Theorem stdio_call_sound_post :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z ->
  (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds mo) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  (* LPS 75d69e00: the reader premise, next to the fd_lookup one -- see stdio_call_sound. *)
  m_channel_reader mo = true ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x109138) M (seg_rom RSEGS) ->
  K [] ->
  (forall R' M' msF' mo',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M su (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS) ->
     realizes RSEGS (mkCfg msF' mo') K) ->
  realizes RSEGS (mkCfg msF mo)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  (* LPS 75d69e00: as stdio_call_sound above (same text, same re-keying).  It differs from
     stdio_call_sound in exactly two places: the HCONT application has one more slot, and the
     last bullet discharges it with HPOST. *)
  intros vals ebs sr kn R M L S Zr msF mo res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0x1203f0 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x681830 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwphi Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr OK RS HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x1203f0 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x681830 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x109138) with (0x109138%bv : word) in RS by (apply bv_eq; reflexivity).
  eapply (as_stdio_write R M L S Zr msF mo su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hrdr.
  - exact OK.
  - exact RS.
  - lia.
  - lia.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' msF' mo' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST OK' SB' HS' RS'.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply (HCONT R' M' msF' mo'); [ | | | exact OK' | exact SB' | exact HS' | exact RS'].
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [(first [clear - Hfd12; lia | lia])|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. (first [clear - Hfd12 Hretv Hq N1; lia | lia]).
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; (first [clear - Hf0 Hfd12 Hf232; lia | lia])|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
    + (* [comment removed for export] *) exact HPOST.
Qed.
