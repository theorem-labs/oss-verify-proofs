(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 260 of its 283 lines of code are new or changed and 121 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Prog/codec_main_owe11.v, with its module paths and module names changed; 370 of its 407 lines of code are new or changed and 246 lines of the source are left out. *)
(* The seven-bit test of OWE11 (SYSEX) in the image-A walk of LLVMFuzzerTestOneInput, 0x82a4c-0x82a84
   (fuzz_codec.c:92-98, seven_bit of lib/Prog/codec_owe.v, inlined in owe()'s default case), and the arithmetic of
   the segment: owe_spec's answer for kind 11 and the executor's values of the tests.
   The loop reads k.bytes[0 .. n) (a0 = a2 = &k.bytes[i], a3 = n - i): an instrumented 1-byte check of a0, lb a4,0(a2),
   bltz a4 -> 0x82730 (the E_RANGE tail), a3 - 1, a0 + 1, a2 + 1, bnez a3 -> 0x82a50, else j 0x82a88. The test of
   each byte depends on the byte, and n is not fixed, so the executor would branch on the count at each pass and
   double its paths on the bytes. o11_loop is the loop as one lemma over machine states, by induction on the passes
   left: each pass runs from a small executor state of its own (CPgWalk.cw_entry0, s4 named the shadow base, one
   read-only byte region on the atom of a2 with the byte as an atom, the engine's shadow entry for a0's byte), and
   the registers it leaves are the next pass's premises; o11_loop0 adds the count test at 0x82a4c (beqz s7). A walk
   re-seats its own state after the loop with lib/Reusable/YI04.v st_ok_after_stretch over O11_CLOB; the loop writes
   no memory. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkImg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ owe_spec for kind 11 ================================ *)
(* the command of a successful SYSEX call: want[0 .. n + 5) and want_display *)
Definition o11_bs (a b : Z) (bytes : list Z) (n : Z) : list Z :=
  [0xf0; 0x13; a; b] ++ firstn (Z.to_nat n) bytes ++ [0xf7].
Definition o11_dp (b : Z) : Z := bit_or_0 ((b =? 0x40) || (b =? 0x30)) 1.

Lemma o11_spec : forall od a b c delta bytes n,
  owe_spec 11 od a b c delta bytes n =
  if 0x7f <? a then (E_ARG, noc)
  else if b =? 0x70 then (E_REFUSED, noc)
  else if 0x7f <? b then (E_RANGE, noc)
  else if 24 <? n + 5 then (E_SPACE, noc)
  else if negb (seven_bit (firstn (Z.to_nat n) bytes)) then (E_RANGE, noc)
  else let '(bs, dp) := owe_sx (u8 a) (u8 b) (firstn (Z.to_nat n) bytes) in (0, (bs, 0, dp)).
Proof. intros. destruct od; reflexivity. Qed.

Lemma o11_ok : forall od a b c delta bytes n, 0 <= a < 128 -> 0 <= b < 128 -> b <> 0x70 -> n + 5 <= 24 ->
  seven_bit (firstn (Z.to_nat n) bytes) = true ->
  owe_spec 11 od a b c delta bytes n = (0, (o11_bs a b bytes n, 0, o11_dp b)).
Proof.
intros od a b c delta bytes n Ha Hb Hb70 Hn H7. rewrite o11_spec.
destruct (Z.ltb_spec 0x7f a); [lia|]. destruct (Z.eqb_spec b 0x70); [lia|].
destruct (Z.ltb_spec 0x7f b); [lia|]. destruct (Z.ltb_spec 24 (n + 5)); [lia|].
rewrite H7. cbn [negb].
assert (Ua : u8 a = a) by (unfold u8; apply Z.mod_small; lia).
assert (Ub : u8 b = b) by (unfold u8; apply Z.mod_small; lia).
rewrite Ua, Ub. unfold owe_sx. rewrite Ua, Ub. reflexivity.
Qed.

Lemma o11_fail_a : forall od a b c delta bytes n, 128 <= a -> fst (owe_spec 11 od a b c delta bytes n) = E_ARG.
Proof. intros. rewrite o11_spec. destruct (Z.ltb_spec 0x7f a); [reflexivity | lia]. Qed.

Lemma o11_fail_70 : forall od a b c delta bytes n, a < 128 -> b = 0x70 ->
  fst (owe_spec 11 od a b c delta bytes n) = E_REFUSED.
Proof.
intros od a b c delta bytes n Ha Hb. rewrite o11_spec. destruct (Z.ltb_spec 0x7f a); [lia|].
destruct (Z.eqb_spec b 0x70); [reflexivity | lia].
Qed.

Lemma o11_fail_b : forall od a b c delta bytes n, a < 128 -> b <> 0x70 -> 128 <= b ->
  fst (owe_spec 11 od a b c delta bytes n) = E_RANGE.
Proof.
intros od a b c delta bytes n Ha Hb Hb2. rewrite o11_spec. destruct (Z.ltb_spec 0x7f a); [lia|].
destruct (Z.eqb_spec b 0x70); [lia|]. destruct (Z.ltb_spec 0x7f b); [reflexivity | lia].
Qed.

Lemma o11_fail_n : forall od a b c delta bytes n, a < 128 -> b <> 0x70 -> b < 128 -> 20 <= n ->
  fst (owe_spec 11 od a b c delta bytes n) = E_SPACE.
Proof.
intros od a b c delta bytes n Ha Hb Hb2 Hn. rewrite o11_spec. destruct (Z.ltb_spec 0x7f a); [lia|].
destruct (Z.eqb_spec b 0x70); [lia|]. destruct (Z.ltb_spec 0x7f b); [lia|].
destruct (Z.ltb_spec 24 (n + 5)); [reflexivity | lia].
Qed.

Lemma o11_fail_s : forall od a b c delta bytes n, a < 128 -> b <> 0x70 -> b < 128 -> n < 20 ->
  seven_bit (firstn (Z.to_nat n) bytes) = false ->
  fst (owe_spec 11 od a b c delta bytes n) = E_RANGE.
Proof.
intros od a b c delta bytes n Ha Hb Hb2 Hn H7. rewrite o11_spec. destruct (Z.ltb_spec 0x7f a); [lia|].
destruct (Z.eqb_spec b 0x70); [lia|]. destruct (Z.ltb_spec 0x7f b); [lia|].
destruct (Z.ltb_spec 24 (n + 5)); [lia|]. rewrite H7. reflexivity.
Qed.

(* ================================ seven_bit over the bytes ================================ *)
Lemma o11_bit7 : forall x, 0 <= x < 256 -> Z.testbit x 7 = (128 <=? x).
Proof.
intros x Hx.
assert (C : forallb (fun y => Bool.eqb (Z.testbit y 7) (128 <=? y)) (map Z.of_nat (seq 0 256)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in C.
specialize (C x ltac:(apply in_map_iff; exists (Z.to_nat x); split; [lia | apply in_seq; lia])).
apply Bool.eqb_prop in C. exact C.
Qed.

Lemma o11_sb_true : forall bs n, 0 <= n -> (Z.to_nat n <= length bs)%nat -> Forall (fun x => 0 <= x < 256) bs ->
  (forall l, 0 <= l < n -> nth (Z.to_nat l) bs 0 < 128) -> seven_bit (firstn (Z.to_nat n) bs) = true.
Proof.
intros bs n Hn Hl Hr H. unfold seven_bit. apply forallb_forall. intros x Hx.
apply (In_nth _ _ 0) in Hx as (j & Hj & Hjx). rewrite length_firstn in Hj.
rewrite nth_firstn in Hjx. destruct (Nat.ltb_spec j (Z.to_nat n)) as [Hlt|Hge]; [|lia].
subst x. rewrite Forall_forall in Hr. pose proof (Hr (nth j bs 0) ltac:(apply nth_In; lia)) as Hrj.
rewrite (o11_bit7 _ Hrj). specialize (H (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id in H.
destruct (Z.leb_spec 128 (nth j bs 0)); [lia | reflexivity].
Qed.

Lemma o11_sb_false : forall bs n j, 0 <= j < n -> (Z.to_nat n <= length bs)%nat ->
  128 <= nth (Z.to_nat j) bs 0 -> nth (Z.to_nat j) bs 0 < 256 -> seven_bit (firstn (Z.to_nat n) bs) = false.
Proof.
intros bs n j Hj Hl H1 H2. unfold seven_bit.
destruct (forallb (fun x => negb (Z.testbit x 7)) (firstn (Z.to_nat n) bs)) eqn:E; [|reflexivity].
exfalso. rewrite forallb_forall in E.
assert (Hin : In (nth (Z.to_nat j) bs 0) (firstn (Z.to_nat n) bs)).
{ assert (Eq : nth (Z.to_nat j) (firstn (Z.to_nat n) bs) 0 = nth (Z.to_nat j) bs 0).
  { rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat n)); [reflexivity | lia]. }
  rewrite <- Eq. apply nth_In. rewrite length_firstn. lia. }
specialize (E _ Hin). rewrite (o11_bit7 (nth (Z.to_nat j) bs 0) ltac:(lia)) in E.
destruct (Z.leb_spec 128 (nth (Z.to_nat j) bs 0)); [discriminate | lia].
Qed.

(* ================================ the executor's values ================================ *)
Lemma o11_U_soff : forall E n v o, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + o < 2 ^ 64 ->
  U E (SOff n o) = v + o.
Proof.
intros E n v o Hn Hv Hvo. rewrite U_SOff, Hn, unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* bltz on a sign-extended byte: taken exactly when the byte has bit 7 set *)
Lemma o11_lt_byte : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  branch_taken BC_LT (sv_denot E (SExt true 8 (SOff n 0))) (sv_denot E (SLit 0)) = (128 <=? v).
Proof.
intros E n v Hn Hv.
assert (D : sv_denot E (SExt true 8 (SOff n 0)) = Z_to_bv 64 (zcanon (bv_swrap 8 v))).
{ pose proof (U_SExt E true 8 (SOff n 0)) as H. rewrite (U_atom E n v Hn) in H by lia. unfold U in H.
  rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SExt true 8 (SOff n 0)))). rewrite H.
  change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small v 256) by lia. reflexivity. }
assert (D0 : sv_denot E (SLit 0) = Z_to_bv 64 0) by reflexivity.
rewrite D, D0.
assert (C : forallb (fun y => Bool.eqb (branch_taken BC_LT (Z_to_bv 64 (zcanon (bv_swrap 8 y))) (Z_to_bv 64 0))
  (128 <=? y)) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C.
specialize (C v ltac:(apply in_map_iff; exists (Z.to_nat v); split; [lia | apply in_seq; lia])).
apply Bool.eqb_prop in C. exact C.
Qed.

(* ================================ registers a pass keeps ================================ *)
Definition O11_CLOB : list (bv 5) := [10; 12; 13; 14; 15]%bv.
Definition o11_sr0 : list sv := sr_set sr_atoms 20%bv (SOff 32 0).
Definition o11_keep_b (sr : list sv) : bool :=
  forallb (fun r => reg_in r O11_CLOB || sv_eqb (sr_get sr r) (sr_get o11_sr0 r)) all_regs.

Lemma o11_atoms_lt : forall r, YP06.sv_atoms_lt 34 (sr_get sr_atoms r) = true.
Proof.
intros r. assert (C : forallb (fun r => YP06.sv_atoms_lt 34 (sr_get sr_atoms r)) all_regs = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in C. exact (C r (YP01.all_regs_in r)).
Qed.

Section k. Context {fx : YK11.FPState}.
Lemma o11_keep : forall regs xs Ev ss H ms, YP06.env_agree 34 (Ereg regs (cw_extra xs)) Ev ->
  getr regs 20%bv = Z_to_bv 64 SB ->
  st_ok tfibsegs Ev ss (restrict H ms) -> o11_keep_b (ss_regs ss) = true ->
  forall r, reg_in r O11_CLOB = false -> getr (ms_regs ms) r = getr regs r.
Proof.
intros regs xs Ev ss H ms HAE R20 HS Hk r Hr.
rewrite (st_ok_restrict_reg tfibsegs H Ev ss ms r HS).
unfold o11_keep_b in Hk. rewrite forallb_forall in Hk. specialize (Hk r (YP01.all_regs_in r)).
rewrite Hr in Hk. cbn [orb] in Hk. rewrite (sv_eqb_eq _ _ Hk).
destruct (Z.eq_dec (bv_unsigned r) 20) as [E20|N20].
- assert (Er : r = 20%bv) by (apply bv_eq; rewrite E20; reflexivity). subst r.
  unfold o11_sr0. rewrite sr_get_set_same by reflexivity. cbn [sv_denot].
  destruct HAE as [HA _]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 32%nat ltac:(lia)), cw_ew_SB.
  symmetry. exact R20.
- unfold o11_sr0. rewrite (sr_get_set_other sr_atoms 20%bv r (SOff 32 0)) by (intros ->; apply N20; reflexivity).
  rewrite (YP06.sv_denot_agree 34 (Ereg regs (cw_extra xs)) Ev (sr_get sr_atoms r) HAE (o11_atoms_lt r)).
  symmetry. apply regs_ok_Ereg.
Qed.
End k.

(* ================================ one pass, and the loop ================================ *)
Definition O11_CNT : Z := 0x82a4c.
Definition O11_LOOP : Z := 0x82a50.
Definition O11_ERR : Z := 0x82730.
Definition O11_OK : Z := 0x82a88.
(* the byte a pass reads, at a2 (atom 12), as the atom 33 *)
Definition o11_lb : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Lemma o11_ra_eq : forall H (m m' : word -> option byte) a len, (forall x, mrestrict H m' x = mrestrict H m x) ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF a len -> range_addressable (aview tfibsegs H m') SHADOW_OFF a len.
Proof.
intros H m m' a len M R x Hx. destruct (R x Hx) as (s & Hs & Ho). exists s. split; [|exact Ho].
rewrite (aview_eq_of tfibsegs H m m' _ (M _)). exact Hs.
Qed.

Ltac o11l_awr :=
  idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia | ] ] end.
(* the memory a pass leaves: its restricted bytes are the old ones (no window) *)
Ltac o11l_mem M :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict ?Hh (ms_mem ?ms2)) |- _ =>
  lazymatch type of M with forall x, mrestrict _ ?m1 x = mrestrict _ ?m0 x =>
    let M2 := fresh "M" in
    assert (M2 : forall x, mrestrict Hh (ms_mem ms2) x = mrestrict Hh m0 x)
      by (let x := fresh "x" in intros x; rewrite <- (M x); apply HFr;
          let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
          intros (r & Hr & Hb); vm_compute in Hr;
          repeat (destruct Hr as [<- | Hr]; [cbn in Hb; lia|]); destruct Hr);
    clear M HFr; try (lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end);
    try (lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end);
    rename M2 into M end end.
Ltac o11l_run M := cw_run o11l_awr; o11l_mem M.
Ltac o11l_run_to M stop := cw_run_to o11l_awr stop; o11l_mem M.
Ltac o11l_rreg HS r Q :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS) end.
Ltac o11l_mkst :=
  lazymatch goal with HS : st_ok _ _ ?ssv (restrict _ ?msv) |- _ =>
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
    let p := eval vm_compute in (ss_pc ssv) in change (ss_pc ssv) with p end.
(* an atom below 34 of the env after a run, as in the pass's start env *)
Ltac o11l_ew Ev n H0 H :=
  assert (H : ew Ev n = _) by (rewrite ?ew_ewset_other by lia; exact H0).
Lemma o11_reg : forall E e (x : word) v, x = sv_denot E e -> U E e = v -> x = Z_to_bv 64 v.
Proof. intros E e x v -> <-. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* the pass's start state: s4 named the shadow base atom 32, the byte at a2, the facts the engine's shadow entry
   for a0's byte needs (a0's range, the shadow base) *)
Definition o11_pAF : list (nat * afact) := [(10%nat, mkAF 4096 AM_HI 0); (32%nat, mkAF SB SB 0)].
Lemma o11_pass_start : forall pc (W : world tfibsegs) regs mem v (a : Z),
  getr regs 20%bv = Z_to_bv 64 SB -> getr regs 10%bv = Z_to_bv 64 a -> getr regs 12%bv = Z_to_bv 64 a ->
  4096 <= a <= AM_HI ->
  0 <= v < 256 -> mbyte tfibsegs (mrestrict (w_H W) mem) a = Some (Z_to_bv 8 v) ->
  st_ok tfibsegs (Ereg regs (cw_extra [v]))
    (mkSS pc o11_sr0 [o11_lb] None (mkFacts o11_pAF [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros pc W regs mem v a R20 R10 R12 Ha Hv Hm.
pose proof (cw_entry0 pc [v] W regs mem) as HS0.
set (E := Ereg regs (cw_extra [v])) in *.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by apply cw_ew_SB.
assert (E33 : ew E 33 = Z_to_bv 64 v) by exact (cw_ew_x regs [v] 0).
assert (E10 : ew E 10 = Z_to_bv 64 a) by (unfold E; rewrite (ew_Ereg_nat regs (cw_extra [v]) 10 10%bv eq_refl); exact R10).
assert (E12 : ew E 12 = Z_to_bv 64 a) by (unfold E; rewrite (ew_Ereg_nat regs (cw_extra [v]) 12 12%bv eq_refl); exact R12).
unfold AM_HI in Ha.
assert (P20 : sv_denot E (SOff 32 0) =
  getr (ms_regs (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)))) 20%bv).
{ change (ms_regs _) with regs. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32. symmetry. exact R20. }
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ 20%bv (SOff 32 0) HS0 eq_refl P20) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
assert (Hr : region_ok tfibsegs E (mrestrict (w_H W) mem) o11_lb).
{ unfold region_ok, o11_lb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E12, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ a 0 1 (SOff 33 0) v); [ | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
  - cbn [sv_denot]. rewrite E33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  - change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. apply cpg_val_mem1; [lia | exact Hm]. }
pose proof (ast_ok_add_region tfibsegs E _ _ o11_lb HS1 eq_refl Hr I) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
refine (st_ok_set_facts tfibsegs E _ _ (mkFacts o11_pAF [] []) HS2 _).
unfold facts_ok, o11_pAF. cbn [f_atoms f_conds f_alias atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E32, !unsigned_lit_small by (unfold SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat split; unfold AM_HI, SB in *; lia.
Qed.

Lemma o11_loop : forall m i n q (bs : list Z) (W : world tfibsegs) regs mem memb md STK sp0 FP ly Sx W0 mem0 md0 own
  lyc Sc k (Q : world tfibsegs -> config -> Prop),
  Z.of_nat m = n - i -> (1 <= m)%nat -> 0 <= i -> n <= 24 -> 4096 <= q -> q + 24 <= AM_HI ->
  ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem md k ->
  getr regs 10%bv = Z_to_bv 64 (q + i) -> getr regs 12%bv = Z_to_bv 64 (q + i) ->
  getr regs 13%bv = Z_to_bv 64 (n - i) -> getr regs 20%bv = Z_to_bv 64 SB ->
  (forall x, mrestrict (w_H W) mem x = mrestrict (w_H W) memb x) ->
  (forall j, 0 <= j < n ->
   aview tfibsegs (w_H W) memb (q + j) = Some (nth (Z.to_nat j) bs 0) /\ 0 <= nth (Z.to_nat j) bs 0 < 256) ->
  range_addressable (aview tfibsegs (w_H W) memb) SHADOW_OFF q n -> amem_range q n ->
  (forall regs' mem' md' j, ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem' md' k ->
   (forall r, reg_in r O11_CLOB = false -> getr regs' r = getr regs r) ->
   i <= j < n -> (forall l, i <= l < j -> nth (Z.to_nat l) bs 0 < 128) -> 128 <= nth (Z.to_nat j) bs 0 ->
   (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) memb x) ->
   SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 O11_ERR) mem' (seg_rom tfibsegs)) md') Q) ->
  (forall regs' mem' md', ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem' md' k ->
   (forall r, reg_in r O11_CLOB = false -> getr regs' r = getr regs r) ->
   (forall l, i <= l < n -> nth (Z.to_nat l) bs 0 < 128) ->
   (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) memb x) ->
   SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 O11_OK) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 O11_LOOP) mem (seg_rom tfibsegs)) md) Q.
Proof.
induction m as [|m IH]; intros i n q bs W regs mem memb md STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k Q
  Hm Hm1 Hi Hn Hq Hq63 HJ R10 R12 R13 R20 M Hbs Hra Ham KE KO; [lia|].
unfold AM_HI in Hq63.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
set (v := nth (Z.to_nat i) bs 0).
destruct (Hbs i ltac:(lia)) as (Av & Hv). fold v in Av, Hv.
assert (Avm : aview tfibsegs (w_H W) mem (q + i) = Some v) by (rewrite (aview_eq_of tfibsegs _ memb mem _ (M _)); exact Av).
destruct (am_mb W mem (q + i) v Avm) as (Hmb & _).
pose proof (o11_pass_start O11_LOOP W regs mem v (q + i) R20 R10 R12 ltac:(unfold AM_HI; lia) Hv Hmb) as HS.
remember (Ereg regs (cw_extra [v])) as E eqn:HEE.
assert (HAE : YP06.env_agree 34 (Ereg regs (cw_extra [v])) E) by (subst E; apply YP06.env_agree_refl).
assert (E10 : ew E 10 = Z_to_bv 64 (q + i)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E12 : ew E 12 = Z_to_bv 64 (q + i)) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = Z_to_bv 64 (n - i)) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact R13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 v) by (subst E; exact (cw_ew_x regs [v] 0)).
clear HEE.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 10 0 1] E (mrestrict (w_H W) mem)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (cw_shent_ra W mem E 10 (q + i) 1); [ | unfold amem_range in *; lia | lia | lia | lia | exact E10 | exact E32].
  apply (o11_ra_eq _ memb mem _ _ M). apply (range_addressable_sub _ _ q n); [exact Hra | lia | lia]. }
(* 0x82a50-0x82a64: the check of a0's byte, lb a4,0(a2), bltz a4 *)
o11l_run M.
cw_branch Hb1.
all: lazymatch type of Hb1 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
  o11l_ew Ev 33%nat E33 F33; rewrite (o11_lt_byte Ev 33 v F33 Hv) in Hb1 end.
- (* the byte has bit 7 set: to 0x82730 *)
  apply Z.leb_le in Hb1.
  o11l_run_to M O11_ERR.
  lazymatch goal with HS1 : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    assert (HAE1 : YP06.env_agree 34 (Ereg regs (cw_extra [v])) Ev) by env_agree_chain HAE;
    pose proof (o11_keep regs [v] Ev ssv _ msv HAE1 R20 HS1 ltac:(vm_compute; reflexivity)) as KP end.
  o11l_mkst.
  apply (KE _ _ _ i); [exact HJ | exact KP | lia | intros l Hl; lia | exact Hb1 | exact M].
- (* bit 7 clear: 0x82a68-0x82a74, a3 - 1, a0 + 1, a2 + 1, bnez a3 *)
  apply Z.leb_gt in Hb1.
  o11l_run M.
  cw_branch Hb2.
  all: lazymatch type of Hb2 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    o11l_ew Ev 13%nat E13 F13;
    rewrite branch_ne_U, (o11_U_soff Ev 13 (n - i) (-1) F13), U_lit in Hb2 by lia end.
  + (* loop back *)
    apply negb_true_iff, Z.eqb_neq in Hb2.
    destruct m as [|m]; [exfalso; lia|].
    o11l_run_to M O11_LOOP.
    lazymatch goal with HS1 : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      assert (HAE1 : YP06.env_agree 34 (Ereg regs (cw_extra [v])) Ev) by env_agree_chain HAE;
      pose proof (o11_keep regs [v] Ev ssv _ msv HAE1 R20 HS1 ltac:(vm_compute; reflexivity)) as KP;
      o11l_ew Ev 10%nat E10 F10; o11l_ew Ev 12%nat E12 F12; o11l_ew Ev 13%nat E13 G13 end.
    o11l_rreg HS (10%bv : bv 5) Q10. o11l_rreg HS (12%bv : bv 5) Q12. o11l_rreg HS (13%bv : bv 5) Q13.
    o11l_mkst.
    eapply (IH (i + 1) n q bs W _ _ memb); [lia | lia | lia | lia | lia | unfold AM_HI; lia | exact HJ | | | | | exact M | exact Hbs
      | exact Hra | exact Ham | | ].
    * apply (o11_reg _ _ _ _ Q10). rewrite (o11_U_soff _ 10 (q + i) 1 F10) by lia. lia.
    * apply (o11_reg _ _ _ _ Q12). rewrite (o11_U_soff _ 12 (q + i) 1 F12) by lia. lia.
    * apply (o11_reg _ _ _ _ Q13). rewrite (o11_U_soff _ 13 (n - i) (-1) G13) by lia. lia.
    * rewrite (KP 20%bv eq_refl). exact R20.
    * intros regs' mem' md' j HJ' Hk' Hj Hl Hb M'. apply (KE regs' mem' md' j HJ'); [ | lia | | exact Hb | exact M'].
      -- intros r Hr. rewrite (Hk' r Hr). exact (KP r Hr).
      -- intros l Hl'. destruct (Z.eq_dec l i) as [->|Hne]; [exact Hb1 | apply Hl; lia].
    * intros regs' mem' md' HJ' Hk' Hl M'. apply (KO regs' mem' md' HJ'); [ | | exact M'].
      -- intros r Hr. rewrite (Hk' r Hr). exact (KP r Hr).
      -- intros l Hl'. destruct (Z.eq_dec l i) as [->|Hne]; [exact Hb1 | apply Hl; lia].
  + (* the last pass: j 0x82a88 *)
    apply negb_false_iff, Z.eqb_eq in Hb2.
    o11l_run_to M O11_OK.
    lazymatch goal with HS1 : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      assert (HAE1 : YP06.env_agree 34 (Ereg regs (cw_extra [v])) Ev) by env_agree_chain HAE;
      pose proof (o11_keep regs [v] Ev ssv _ msv HAE1 R20 HS1 ltac:(vm_compute; reflexivity)) as KP end.
    o11l_mkst.
    apply (KO _ _ _ HJ KP); [|exact M].
    intros l Hl. assert (El : l = i) by lia. subst l. exact Hb1.
Qed.

(* the count test 0x82a4c (beqz s7, s7 = n) and the loop *)
Lemma o11_loop0 : forall n q (bs : list Z) (W : world tfibsegs) regs mem memb md STK sp0 FP ly Sx W0 mem0 md0 own
  lyc Sc k (Q : world tfibsegs -> config -> Prop),
  0 <= n <= 24 -> 4096 <= q -> q + 24 <= AM_HI ->
  ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem md k ->
  getr regs 10%bv = Z_to_bv 64 q -> getr regs 12%bv = Z_to_bv 64 q ->
  getr regs 13%bv = Z_to_bv 64 n -> getr regs 23%bv = Z_to_bv 64 n -> getr regs 20%bv = Z_to_bv 64 SB ->
  (forall x, mrestrict (w_H W) mem x = mrestrict (w_H W) memb x) ->
  (forall j, 0 <= j < n ->
   aview tfibsegs (w_H W) memb (q + j) = Some (nth (Z.to_nat j) bs 0) /\ 0 <= nth (Z.to_nat j) bs 0 < 256) ->
  range_addressable (aview tfibsegs (w_H W) memb) SHADOW_OFF q n -> amem_range q n ->
  (forall regs' mem' md' j, ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem' md' k ->
   (forall r, reg_in r O11_CLOB = false -> getr regs' r = getr regs r) ->
   0 <= j < n -> (forall l, 0 <= l < j -> nth (Z.to_nat l) bs 0 < 128) -> 128 <= nth (Z.to_nat j) bs 0 ->
   (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) memb x) ->
   SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 O11_ERR) mem' (seg_rom tfibsegs)) md') Q) ->
  (forall regs' mem' md', ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem' md' k ->
   (forall r, reg_in r O11_CLOB = false -> getr regs' r = getr regs r) ->
   (forall l, 0 <= l < n -> nth (Z.to_nat l) bs 0 < 128) ->
   (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) memb x) ->
   SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 O11_OK) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 O11_CNT) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros n q bs W regs mem memb md STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k Q
  Hn Hq Hq63 HJ R10 R12 R13 R23 R20 M Hbs Hra Ham KE KO.
unfold AM_HI in Hq63.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry0 O11_CNT [] W regs mem) as HS0.
remember (Ereg regs (cw_extra [])) as E eqn:HEE.
assert (HAE : YP06.env_agree 34 (Ereg regs (cw_extra [])) E) by (subst E; apply YP06.env_agree_refl).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E23 : ew E 23 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E12 : ew E 12 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact R13).
assert (P20 : sv_denot E (SOff 32 0) =
  getr (ms_regs (restrict (w_H W) (mkst regs (Z_to_bv 64 O11_CNT) mem (seg_rom tfibsegs)))) 20%bv).
{ change (ms_regs _) with regs. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32. symmetry. exact R20. }
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ 20%bv (SOff 32 0) HS0 eq_refl P20) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS. clear HS0 HEE.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
cw_branch Hb.
all: rewrite branch_eq_U, (U_atom E 23 n E23), U_lit in Hb by lia.
- (* n = 0: to 0x82a88 *)
  apply Z.eqb_eq in Hb.
  o11l_run_to M O11_OK.
  lazymatch goal with HS1 : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    assert (HAE1 : YP06.env_agree 34 (Ereg regs (cw_extra [])) Ev) by env_agree_chain HAE;
    pose proof (o11_keep regs [] Ev ssv _ msv HAE1 R20 HS1 ltac:(vm_compute; reflexivity)) as KP end.
  o11l_mkst.
  apply (KO _ _ _ HJ KP); [intros l Hl; lia | exact M].
- (* n <> 0: the loop *)
  apply Z.eqb_neq in Hb.
  o11l_run_to M O11_LOOP.
  lazymatch goal with HS1 : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    assert (HAE1 : YP06.env_agree 34 (Ereg regs (cw_extra [])) Ev) by env_agree_chain HAE;
    pose proof (o11_keep regs [] Ev ssv _ msv HAE1 R20 HS1 ltac:(vm_compute; reflexivity)) as KP;
    o11l_ew Ev 10%nat E10 F10; o11l_ew Ev 12%nat E12 F12; o11l_ew Ev 13%nat E13 F13 end.
  o11l_rreg HS (10%bv : bv 5) Q10. o11l_rreg HS (12%bv : bv 5) Q12. o11l_rreg HS (13%bv : bv 5) Q13.
  o11l_mkst.
  apply (o11_loop (Z.to_nat n) 0 n q bs W _ _ memb _ STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k Q);
    [lia | lia | lia | lia | lia | unfold AM_HI; lia | exact HJ | | | | | exact M | exact Hbs | exact Hra | exact Ham | | ].
  + apply (o11_reg _ _ _ _ Q10). rewrite (U_atom _ 10 q F10) by lia. lia.
  + apply (o11_reg _ _ _ _ Q12). rewrite (U_atom _ 12 q F12) by lia. lia.
  + apply (o11_reg _ _ _ _ Q13). rewrite (U_atom _ 13 n F13) by lia. lia.
  + rewrite (KP 20%bv eq_refl). exact R20.
  + intros regs' mem' md' j HJ' Hk' Hj Hl Hb' M'. apply (KE regs' mem' md' j HJ'); [ | lia | exact Hl | exact Hb' | exact M'].
    intros r Hr. rewrite (Hk' r Hr). exact (KP r Hr).
  + intros regs' mem' md' HJ' Hk' Hl M'. apply (KO regs' mem' md' HJ'); [ | exact Hl | exact M'].
    intros r Hr. rewrite (Hk' r Hr). exact (KP r Hr).
Qed.
End b.
