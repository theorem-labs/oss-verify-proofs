(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the first half of a turn of the image-A walk of reac-repacer/fuzz_uci's LLVMFuzzerTestOneInput, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_early.v (input bytes as regions added after the branch that guards them, each shadow check closed by the token rule against the input block, the kept bytes of each run) and LLVMFuzzerTestOneInput_seg_entry.v (the seat and the closing lemma): fuzz_uci.asan's byte loop of cur, its length byte and the slice length. *)
(* LLVMFuzzerTestOneInput_seg_turna: u_turn_a_ok : u_turn_a_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v).

   The run, by the Pa engine from the head of turn i (+0xa8) to +0x130, generic in i (the run reads no turn register):
   `sw zero, 8(sp)`, then four times `bgeu s8, s0`: the byte at p + s8 (its shadow check, `lbu`, s8 += 1) or 0,
   stored at sp + 8 + j; then the length byte the same way; then s3 = n - s8 and `bltu s3, a0` / `mv s3, a0`:
   s3 = min(n - s8, length byte). The input address p + s8 is the atom 32 through the alias fact
   (s1 + s8 = atom 32), so that the k-th loaded byte is the region (atom 32, offset k) added right after the branch that
   proves p + s8 + k < n; its shadow check leaves the obligation that this byte is addressable, which the input block
   discharges (YCbq.v obl_of_block). Once a `bgeu` is taken the later ones are decided by its condition, so the branches
   form a comb: k = 0 .. 4 bytes read and then the end of the input, or all five read and the `bltu` split. The run
   writes only [sp1 + 8, sp1 + 12) (the stack region's window); everything else, the saved words and the stored
   results among it, is kept (kept_of_frame). *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YE00 YE01 YO09 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  UciPSyms UciPList UciPAddr UciPPa UciPPaLib UciPImg UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0xa8                                       *)
(* ------------------------------------------------------------------ *)

(* Atoms: registers 0 .. 31, 32 = p + s8 (the alias of s1 + s8), 33 .. 37 the five input bytes from p + s8 on (0 past
   the end). Region: the cur buffer [sp + 8, sp + 12), written. *)
Definition ta_stack : YP09.region := YP09.mkRegion (Some 2%nat) 8 12 8 12 [].
Definition ta_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (22%nat, mkAF SBv SBv 0); (8%nat, mkAF 0 (2 ^ 26 - 1) 0);
           (9%nat, PTR 0); (24%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, PTR 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0);
           (37%nat, mkAF 0 255 0)] [] [(SAlu ALU_ADD (SOff 9 0) (SOff 24 0), SOff 32 0)].
Definition ss_oh : sstate := mkSS U_OH sr_atoms [ta_stack] None ta_facts.
Definition ta_extra (x v0 v1 v2 v3 v4 : Z) : list word := [w64 x; w64 v0; w64 v1; w64 v2; w64 v3; w64 v4].
(* The k-th loaded byte, read only after the branch that proves it lies in the input. *)
Definition ta_breg (j : nat) : YP09.region :=
  YP09.mkRegion (Some 32%nat) (Z.of_nat j) (Z.of_nat j + 1) 0 0 [YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j) 0))].
(* The input byte at offset k (0 past the end). *)
Definition ta_byte (pl : list byte) (k : Z) : Z := bv_unsigned (nth (Z.to_nat k) pl (Z_to_bv 8 0)).
Lemma ta_byte_range : forall pl k, 0 <= ta_byte pl k < 256.
Proof. intros pl k. unfold ta_byte. exact (bv_unsigned_in_range 8 _). Qed.

(* The little-endian bytes of a 4-byte value. *)
Lemma ta_le4 : forall c0 c1 c2 c3 (k : nat), 0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  (k < 4)%nat -> le_byte (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3) 4 k = nth k [c0; c1; c2; c3] 0.
Proof.
intros c0 c1 c2 c3 k H0 H1 H2 H3 Hk. unfold le_byte.
rewrite (Z.mod_small _ (2 ^ (8 * Z.of_nat 4))) by (change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia).
rewrite Z.shiftr_div_pow2 by lia.
do 4 (destruct k as [|k]; [cbn [nth Z.of_nat]; change (8 * Z.of_nat _) with (8 * Z.of_nat k) || idtac;
  first [change (2 ^ (8 * Z.of_nat 0)) with 1 | change (2 ^ (8 * Z.of_nat 1)) with 256
        | change (2 ^ (8 * Z.of_nat 2)) with 65536 | change (2 ^ (8 * Z.of_nat 3)) with 16777216 | idtac];
  Z.div_mod_to_equations; lia|]).
lia.
Qed.

(* U of `s3 = n - s8` as the run writes it. *)
Lemma ta_U_rest : forall E a b c va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb -> 0 <= va < 2 ^ 64 -> 0 <= vb < 2 ^ 64 ->
  0 <= va + c - vb < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff a c) (SMd M_MUL (SOff b 0) (SLit (-1)))) = va + c - vb.
Proof.
intros E a b c va vb Ha Hb Hva Hvb Hr.
rewrite U_SAlu, U_SMd, U_SOff, U_SOff, U_SLit, Ha, Hb, !unsigned_lit_small by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64. rewrite Z.add_0_r.
rewrite <- Zmult_mod, <- Zplus_mod.
replace (va + c + vb * -1) with (va + c - vb) by lia. apply Z.mod_small. lia.
Qed.

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ uci_listing PI_uci).
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).
Definition ETA (regs : bvmap 5 word) (x v0 v1 v2 v3 v4 : Z) : env := Eimg (PI := PI_uci) (Ereg regs (ta_extra x v0 v1 v2 v3 v4)).

Lemma ta_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem (sp1 n p off v0 v1 v2 v3 v4 : Z),
  getr regs 2 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 16 = 0 ->
  (forall a, sp1 + 8 <= a < sp1 + 12 -> apresent (w_H W) mem a) ->
  getr regs 8 = w64 n -> 0 <= n < 2 ^ 26 -> getr regs 9 = w64 p -> 4096 <= p -> p + n <= 140737479966720 ->
  getr regs 22 = w64 SHADOW_OFF -> getr regs 24 = w64 off -> 0 <= off <= n ->
  0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> 0 <= v4 < 256 ->
  st_ok_pi SEGS VAL (ETA regs (p + off) v0 v1 v2 v3 v4) ss_oh
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + U_OH)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sp1 n p off v0 v1 v2 v3 v4 R2 Hsp Hsp16 Hpres R8 Hn R9 Hp Hpn R22 R24 Hoff Hv0 Hv1 Hv2 Hv3 Hv4.
rewrite restrict_mkst_fx. unfold ss_oh.
set (E := ETA regs (p + off) v0 v1 v2 v3 v4).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (ta_extra (p + off) v0 v1 v2 v3 v4)) k)
  by (intros k Hk; unfold E, ETA; apply Eimg_low; exact Hk).
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; rewrite EL by (pose proof (bv_unsigned_in_range 5 r) as Hr; change (bv_modulus 5) with 32 in Hr; unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (ta_extra (p + off) v0 v1 v2 v3 v4) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite (ER 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ta_stack. constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split].
  + cbn [ta_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, (ER 22%nat 22%bv eq_refl), (ER 8%nat 8%bv eq_refl), (ER 9%nat 9%bv eq_refl), (ER 24%nat 24%bv eq_refl).
    pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
    pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
    cbn [nth ta_extra Nat.add] in E32, E33, E34, E35, E36, E37.
    rewrite E32, E33, E34, E35, E36, E37.
    rewrite R22, R8, R9, R24. unfold w64.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SBv, SHADOW_OFF in *; first [lia | reflexivity].
  + cbn [ta_facts f_conds conds_ok]. exact I.
  + cbn [ta_facts f_alias alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal.
    pose proof (EX 0%nat ltac:(lia)) as E32. cbn [nth ta_extra Nat.add] in E32.
    rewrite U_SAlu, !U_SOff, (ER 9%nat 9%bv eq_refl), (ER 24%nat 24%bv eq_refl), E32.
    rewrite R9, R24. unfold w64. rewrite !unsigned_lit_small by lia. cbn [zalu_raw]. rewrite !Z.add_0_r.
    rewrite !(zcanon_id p), !(zcanon_id off) by (unfold M64; lia). reflexivity.
Qed.

Lemma ta_aview_vm1 : forall H (m : word -> option byte) a v, val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 ->
  aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. unfold aview. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv.
cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
cbn [Z.of_nat Z.mul Pos.mul]. rewrite Z.shiftr_0_r. rewrite !Z.mod_small; change (2 ^ 8) with 256 in *; lia.
Qed.

(* The closing of a path at +0x130: the final symbolic state of the run, with the registers it leaves (s3 = len,
   s8 = off + kk, the others as at +0xa8) and the four stored bytes of cur, is u_st_pre. *)
Lemma ta_close : forall (B : asyms) (MT : ameter_ops) (XL : Z -> Z) ly S (W0 : world SEGS) regs mem md p n pl M
    (i : Z) ly' S' (W : world SEGS) (regs' : bvmap 5 word) mem' md' (off mm : Z) (vs : list Z)
    (x v0 v1 v2 v3 v4 : Z) Ex ss ms md'' (kk len : Z) e0 e1 e2 e3 c0 c1 c2 c3,
  let cx := mkUCx fx ly S W0 regs mem md p n pl M in
  u_core B cx ly' S' W regs' mem' md' (i * U_EV_TURN) -> u_meter MT XL cx S' i ->
  getr regs' 8 = w64 n -> getr regs' 9 = w64 p -> getr regs' 18 = w64 mm -> (mm = U_MM0 \/ mm = U_MM1) ->
  getr regs' 22 = w64 SHADOW_OFF -> getr regs' 23 = w64 i -> getr regs' 24 = w64 off ->
  getr regs' 25 = w64 (u_sp1 cx + 0x1c) -> getr regs' 26 = w64 5 ->
  0 <= off -> u_res cx (aview SEGS (w_H W) mem') i vs -> 2 ^ 46 <= u_sp1 cx <= 2 ^ 47 ->
  @ajournal rc AE2k.tfib_sink_head SEGS B LLVMF_STK (u_sp0 cx) [] ly S W0 mem md [] ly' S' W (ms_mem ms) md''
    (i * U_EV_TURN) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (u_sp1 cx + 8 <= a < u_sp1 cx + 12) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem' a) ->
  st_ok_pi SEGS VAL Ex ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = U_PRE ->
  (forall k, (k < 512)%nat -> ew Ex k = ew (ETA regs' x v0 v1 v2 v3 v4) k) ->
  In (YP09.mkRegion (Some 2%nat) 8 12 8 12 [YP09.mkChunk 11 (CVal 1 e3); YP09.mkChunk 10 (CVal 1 e2);
                                              YP09.mkChunk 9 (CVal 1 e1); YP09.mkChunk 8 (CVal 1 e0)]) (ss_mem ss) ->
  sv_denot Ex e0 = w64 c0 -> sv_denot Ex e1 = w64 c1 -> sv_denot Ex e2 = w64 c2 -> sv_denot Ex e3 = w64 c3 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  sr_get (ss_regs ss) 2 = SOff 2 0 -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
  sr_get (ss_regs ss) 8 = SOff 8 0 -> sr_get (ss_regs ss) 9 = SOff 9 0 -> sr_get (ss_regs ss) 18 = SOff 18 0 ->
  sr_get (ss_regs ss) 22 = SOff 22 0 -> sr_get (ss_regs ss) 23 = SOff 23 0 -> sr_get (ss_regs ss) 24 = SOff 24 kk ->
  sr_get (ss_regs ss) 25 = SOff 25 0 -> sr_get (ss_regs ss) 26 = SOff 26 0 -> sr_get (ss_regs ss) 27 = SOff 27 0 ->
  getr (ms_regs ms) 19 = w64 len ->
  0 <= kk -> 0 <= len <= PR.REPLY_MAX -> off + kk + len <= n -> n < 2 ^ 26 -> 0 <= i <= 5 ->
  u_st_pre B MT XL cx i W (mkCfg ms md'').
Proof.
intros B MT XL ly S W0 regs mem md p n pl M i ly' S' W regs' mem' md' off mm vs x v0 v1 v2 v3 v4 Ex ss ms md'' kk len
  e0 e1 e2 e3 c0 c1 c2 c3 cx HC HM R8 R9 R18 Hmm R22 R23 R24 R25 R26 Hoff HRES Hsp1 HJ KR HS Hrv Hpc EA Hin
  D0 D1 D2 D3 B0 B1 B2 B3 S2 S3 S4 S8 S9 S18 S22 S23 S24 S25 S26 S27 R19 Hkk Hlen Hsum Hn Hi.
pose proof HC as (_ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
assert (SVR : Forall (fun o : Z * Z => 8 <= fst o <= 96) uci_saved_at)
  by (unfold uci_saved_at; repeat constructor; cbn [fst]; lia).
assert (Hsp0 : u_sp0 cx = u_sp1 cx + 144) by (unfold u_sp1, U_FRAME; lia).
assert (ER : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew Ex k = getr regs' r).
{ intros k r Hk Hkr. rewrite (EA k) by lia. unfold ETA. apply ew_Eimg_Ereg_nat. exact Hkr. }
assert (RG : forall (r : bv 5) e, sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot Ex e).
{ intros r e He. rewrite <- He. exact (st_ok_pi_restrict_reg (w_H W) Ex ss ms r HS). }
assert (RK : forall (r : bv 5) (k : nat), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> sr_get (ss_regs ss) r = SOff k 0 ->
  getr (ms_regs ms) r = getr regs' r).
{ intros r k Hk Hkr He. rewrite (RG r _ He). cbn [sv_denot]. rewrite (ER k r Hk Hkr), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (R2 : getr regs' 2 = w64 (u_sp1 cx)) by (unfold w64; rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Usp : bv_unsigned (ew Ex 2) = u_sp1 cx) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
pose proof (st_ok_pi_restrict_mkst (w_H W) Ex ss ms HS Hrv) as Hms.
assert (HR0 : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem ms))
  (YP09.mkRegion (Some 2%nat) 8 12 8 12 [YP09.mkChunk 11 (CVal 1 e3); YP09.mkChunk 10 (CVal 1 e2);
                                          YP09.mkChunk 9 (CVal 1 e1); YP09.mkChunk 8 (CVal 1 e0)])).
{ destruct (st_ok_mem_ok SEGS Ex (abs_ss VAL ss) (restrict (w_H W) ms) HS) as (_ & Hrs & _).
  exact (proj1 (Forall_forall _ _) Hrs _ ltac:(destruct ss; exact Hin)). }
assert (CB : forall od e c, In (YP09.mkChunk od (CVal 1 e)) [YP09.mkChunk 11 (CVal 1 e3); YP09.mkChunk 10 (CVal 1 e2);
                                          YP09.mkChunk 9 (CVal 1 e1); YP09.mkChunk 8 (CVal 1 e0)] ->
  sv_denot Ex e = w64 c -> 0 <= c < 256 -> aview SEGS (w_H W) (ms_mem ms) (u_sp1 cx + od) = Some c).
{ intros od e c Hc He Hcr. apply ta_aview_vm1; [|exact Hcr].
  exact (field_of_region Ex _ 2 (u_sp1 cx) _ 8 12 8 12 od 1 e c HR0 Usp Hc He ltac:(change (8 * Z.of_N 1) with 8; lia) ltac:(cbv; discriminate)). }
rewrite Hms, Hpc.
exists ly', S', (ms_regs ms), (ms_mem ms), md'', (off + kk), len, mm, (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3), vs.
split; [reflexivity|].
split.
{ split; [exact HJ|]. split; [exact Hfrs|].
  split; [unfold spZ; rewrite (RK 2%bv 2%nat) by (lia || reflexivity || exact S2); exact Hsp|].
  split; [rewrite (RK 3%bv 3%nat) by (lia || reflexivity || exact S3); exact Hgp|].
  split; [rewrite (RK 4%bv 4%nat) by (lia || reflexivity || exact S4); exact Htp|].
  split; [rewrite (RK 27%bv 27%nat) by (lia || reflexivity || exact S27); exact H27|].
  split; [|exact Hperm].
  unfold u_saved in *. rewrite Forall_forall in Hsv, SVR |- *. intros o Ho.
  rewrite <- (Hsv o Ho). apply rdword_kept. intros k Hk. pose proof (SVR o Ho) as Hb.
  apply KR; lia. }
split; [exact HM|].
split; [rewrite (RK 8%bv 8%nat) by (lia || reflexivity || exact S8); exact R8|].
split; [rewrite (RK 9%bv 9%nat) by (lia || reflexivity || exact S9); exact R9|].
split; [rewrite (RK 18%bv 18%nat) by (lia || reflexivity || exact S18); exact R18|].
split; [exact Hmm|].
split; [exact R19|].
split; [rewrite (RK 22%bv 22%nat) by (lia || reflexivity || exact S22); exact R22|].
split; [rewrite (RK 23%bv 23%nat) by (lia || reflexivity || exact S23); exact R23|].
split; [rewrite (RG 24%bv _ S24); cbn [sv_denot]; rewrite (ER 24%nat 24%bv) by (lia || reflexivity); rewrite R24;
        unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RK 25%bv 25%nat) by (lia || reflexivity || exact S25); exact R25|].
split; [rewrite (RK 26%bv 26%nat) by (lia || reflexivity || exact S26); exact R26|].
split; [lia|]. split; [lia|]. split; [unfold cx; cbn [u_n]; lia|]. split; [lia|].
split.
{ intros k Hk. rewrite (ta_le4 c0 c1 c2 c3 k B0 B1 B2 B3 Hk).
  do 4 (destruct k as [|k]; [cbn [nth]; first
    [ rewrite Z.add_0_r; replace (u_sp1 cx + 8) with (u_sp1 cx + 8) by lia; apply (CB 8 e0 c0); [cbn; tauto | exact D0 | exact B0]
    | replace (u_sp1 cx + 8 + Z.of_nat 1) with (u_sp1 cx + 9) by lia; apply (CB 9 e1 c1); [cbn; tauto | exact D1 | exact B1]
    | replace (u_sp1 cx + 8 + Z.of_nat 2) with (u_sp1 cx + 10) by lia; apply (CB 10 e2 c2); [cbn; tauto | exact D2 | exact B2]
    | replace (u_sp1 cx + 8 + Z.of_nat 3) with (u_sp1 cx + 11) by lia; apply (CB 11 e3 c3); [cbn; tauto | exact D3 | exact B3] ]|]).
  lia. }
destruct HRES as (Hl & Hint & Hrd). split; [exact Hl|]. split; [exact Hint|].
intros j Hj k Hk. rewrite KR; [exact (Hrd j Hj k Hk) | lia | lia].
Qed.

(* The k-th loaded byte as a region of the run: the input byte at x + j holds v. *)
Lemma ta_breg_ok : forall Ex (j : nat) (m : word -> option byte) (x v : Z),
  bv_unsigned (ew Ex 32) = x -> ew Ex (33 + j) = w64 v -> 0 <= v < 256 -> 0 <= x -> x + Z.of_nat j + 1 <= 2 ^ 64 ->
  val_mem SEGS m (x + Z.of_nat j) 1 v ->
  region_ok SEGS Ex m (ta_breg j).
Proof.
intros Ex j m x v Hx Hv Hr H0 H1 Hm. unfold region_ok, ta_breg.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hx.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS Ex m x (Z.of_nat j) 1 (SOff (33 + j) 0) v);
  [cbn [sv_denot]; rewrite Hv; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
  | change (8 * Z.of_N 1) with 8; lia | zside | exact Hm].
Qed.

(* The input byte at p + k (k < n) of the entry, kept by the journal's block clause. *)
Lemma ta_input_vm : forall (B : asyms) STK sp0 ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' k0
    (p n : Z) (pl : list byte) (k : Z),
  @ajournal rc AE2k.tfib_sink_head SEGS B STK sp0 [] ly S W mem md [] ly' S' W' mem' md' k0 ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
  garr8 SEGS (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) -> n = Z.of_nat (length pl) ->
  0 <= k < n -> val_mem SEGS (mrestrict (w_H W') mem') (p + k) 1 (ta_byte pl k).
Proof.
intros B STK sp0 ly S W mem md ly' S' W' mem' md' k0 p n pl k HJ Hin Hin' Hg Hlen Hk.
assert (Hil : (Z.to_nat k < length (map (fun b : byte => bv_unsigned b) pl))%nat) by (rewrite length_map; lia).
destruct (Hg (Z.to_nat k) Hil) as [Hv _].
replace (nth (Z.to_nat k) (map (fun b : byte => bv_unsigned b) pl) 0) with (ta_byte pl k) in Hv.
2: { unfold ta_byte. change 0 with ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0)). rewrite map_nth. reflexivity. }
rewrite Z2Nat.id in Hv by lia.
apply (val_mem_moved SEGS (w_H W) (w_H W') mem mem' (p + k) (p + k) 1 _); [|exact Hv].
intros j Hj. cbn in Hj. replace (p + k + j) with (p + (k + j)) by lia.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos n ltac:(lia)) as Hrn.
apply (F2 p n (k + j) Hin Hin'); [lia | intros (rg & [] & _)].
Qed.

Lemma ta_dv_atom : forall Ex (k : nat) v, ew Ex k = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot Ex (SOff k 0) = w64 v.
Proof. intros Ex k v Hv Hr. cbn [sv_denot]. rewrite Hv. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. Qed.

Lemma ta_geu_Z : forall Ex (j : Z) off n, ew Ex 24 = w64 off -> ew Ex 8 = w64 n -> 0 <= off < 2 ^ 26 -> 0 <= n < 2 ^ 26 ->
  0 <= j <= 5 -> branch_taken BC_GEU (sv_denot Ex (SOff 24 j)) (sv_denot Ex (SOff 8 0)) = negb (off + j <? n).
Proof.
intros Ex j off n H24 H8 Ho Hn Hj. rewrite branch_geu_U.
rewrite (U_atom_off Ex 24 off j H24) by lia. rewrite (U_atom Ex 8 n H8) by lia. reflexivity.
Qed.

Lemma ta_ltu0 : forall Ex v, branch_taken BC_LTU (sv_denot Ex v) (sv_denot Ex (SLit 0)) = false.
Proof.
intros Ex v. rewrite branch_ltu_U, U_lit by lia. pose proof (U_range Ex v) as Hr. apply Z.ltb_ge. lia.
Qed.
End en.

(* ------------------------------------------------------------------ *)
(* 2. The segment                                                       *)
(* ------------------------------------------------------------------ *)

(* The write rights of a run: the cur buffer (stack region on atom 2 = sp1 = sp0 - 0x90) in the entry's stack window;
   the input bytes read only. *)
Ltac ta_awr U2 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-144));
    [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U2; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |] ].
(* After a run: every byte outside the cur buffer is the +0xa8 byte (seg_early.v e_kupd's form). *)
Ltac ta_kupd KR U2 :=
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict ?H ?m0) (mrestrict ?H ?m1),
                      HG : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
  lazymatch type of KR with forall a, _ -> ~ (?lo <= a < ?hi) -> aview _ _ _ a = aview _ _ ?mb a =>
    let KR2 := fresh "KR" in
    assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m1 a = aview tfibsegs H mb a);
    [ intros a Ha Hn; transitivity (aview tfibsegs H m0 a); [| exact (KR a Ha Hn)];
      refine (kept_of_frame Ex rsx H m0 m1 (fun z => lo <= z < hi) HFr _ a Ha Hn);
      intros bb wlo whi z Hin Hr;
      let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
      rewrite ?ew_ewset_other in Hr by lia; cbv beta; rewrite ?U2 in Hr; lia
    | clear KR HFr HG; rename KR2 into KR ]
  end end.
Ltac ta_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let md2 := fresh "md" in set (md2 := mdx) in *; clearbody md2 end.
Ltac ta_norm HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?ms => let v := eval vm_compute in ss in change ss with v in HS end.
(* The value of an atom of the seat in the current environment. *)
Ltac ta_ew Eq := rewrite ?ew_ewset_other by lia; exact Eq.

Section sg. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
(* The obligation of a checked input byte at p + off + j (j < n - off): the input block's shadow. *)
Local Ltac ta_obl LAWS HJ Hinb E22 E32 p n off :=
  eapply (obl_of_block tfibsegs B LAWS _ _ _ _ _ _ (SOff 22 0) _ 1 p n (proj1 HJ) (Hinb ltac:(lia)));
  [ rewrite (U_atom _ 22 SHADOW_OFF) by (first [ta_ew E22 | unfold SHADOW_OFF; lia]); reflexivity
  | rewrite (U_atom_off _ 32 (p + off)) by (first [ta_ew E32 | lia]); lia
  | rewrite (U_atom_off _ 32 (p + off)) by (first [ta_ew E32 | lia]); pose proof (req_size_pos n ltac:(lia)); lia ].
(* One run to the next stop (a branch or +0x130), with its obligations, write rights and kept bytes. *)
Local Ltac ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off :=
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 304; [ ta_obl LAWS HJ Hinb E22 E32 p n off .. | ta_awr U2 | ];
  ta_kupd KR U2; ta_md.
(* The branch `bgeu s8 + j, s0` as a fact about off + j and n. *)
Local Ltac ta_br_geu j E24 E8 off n :=
  match goal with Hc : branch_taken BC_GEU _ _ = _ |- _ =>
    rewrite (ta_geu_Z _ j off n) in Hc by (first [ta_ew E24 | ta_ew E8 | lia]);
    first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
    let Hb := fresh "Hb" in rename Hc into Hb
  end.
(* The k-th loaded byte added as a region (after the branch that proves off + j < n). *)
Local Ltac ta_addb j kj HS HJ U32 U2 Ej Hvj Hin0 Hinb Hgarr Hlen ly S W mem md ly' S' W' p n pl off :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
    let HS2 := fresh "HS" in
    pose proof (st_ok_pi_add_region Ex ss (restrict Hh msx) (ta_breg j) HS eq_refl) as HS2;
    lazymatch type of HS2 with ?A -> ?Bq -> _ =>
      let Hrok := fresh "Hrok" in let Hdj := fresh "Hdj" in
      assert (Hrok : A);
      [ cbn [ms_mem restrict];
        eapply (ta_breg_ok Ex j (mrestrict Hh (ms_mem msx)) (p + off) _);
        [ rewrite ?ew_ewset_other by lia; exact U32 | ta_ew Ej | exact Hvj | lia | lia
        | replace (p + off + Z.of_nat j) with (p + kj) by lia;
          exact (ta_input_vm B LLVMF_STK _ ly S W mem md ly' S' W' _ _ _ p n pl kj HJ
                   (Hin0 ltac:(lia)) (Hinb ltac:(lia)) Hgarr Hlen ltac:(lia)) ]
      | assert (Hdj : Bq);
        [ let rs2 := eval vm_compute in (ss_mem ss) in change (all_disjoint Ex (ta_breg j) rs2);
          cbn [all_disjoint]; unfold extent_disjoint, ta_breg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_nat];
          rewrite ?ew_ewset_other by lia; rewrite ?U32, ?U2; repeat split; lia
        | specialize (HS2 Hrok Hdj); clear HS Hrok Hdj; rename HS2 into HS ] ]
    end
  end; ta_norm HS.
(* A stored byte's value at the closing: an input byte (atom 33 + j) or 0. *)
Local Ltac ta_dv E33 E34 E35 E36 E37 :=
  first [ eapply ta_dv_atom; [rewrite ?ew_ewset_other by lia; first [exact E33 | exact E34 | exact E35 | exact E36 | exact E37] | lia]
        | reflexivity ].
(* s3 at the closing, as the final state holds it. *)
Local Ltac ta_s3_get HS :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ss msx 19 HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) 19) in change (sr_get (ss_regs ss) 19) with e end.
(* The closing at +0x130 by ta_close (FIN is ta_close at this segment's context). *)
Local Ltac ta_fin FIN HJ KR HS E33 E34 E35 E36 E37 s3tac :=
  apply SRr_ret; eapply FIN;
  [ exact HJ | exact KR | exact HS | reflexivity | reflexivity
  | intros kk Hkk; rewrite ?ew_ewset_other by lia; reflexivity
  | cbn [ss_mem In]; repeat (first [left; reflexivity | right])
  | ta_dv E33 E34 E35 E36 E37 | ta_dv E33 E34 E35 E36 E37 | ta_dv E33 E34 E35 E36 E37 | ta_dv E33 E34 E35 E36 E37
  | lia | lia | lia | lia
  | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
  | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
  | s3tac
  | lia | unfold PR.REPLY_MAX; lia | lia | lia | lia ].
(* The end of the input before byte j: every later `bgeu` is decided by its condition, a0 = 0 at the `bltu`, whose
   taken arm (an unsigned value below 0) is refuted; then +0x130 with len = 0. *)
Local Ltac ta_past FIN RUN RUNTO BR HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off E33 E34 E35 E36 E37 :=
  ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off;
  psrr_branch_tok RUN BR HS SHOK Bspan;
  [ match goal with Hc : branch_taken BC_LTU _ _ = true |- _ => rewrite ta_ltu0 in Hc; discriminate Hc end
  | match goal with Hc : branch_taken BC_LTU _ _ = false |- _ => clear Hc end;
    ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off;
    ta_fin FIN HJ KR HS E33 E34 E35 E36 E37 ltac:(ta_s3_get HS; reflexivity) ].


Theorem u_turn_a_ok : u_turn_a_stmt B MT XL RLO RHI.
Proof.
intros HP cx i W' c' Hi HB HOH.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
destruct cx as [fx ly S W regs mem md p n pl M].
unfold u_base, tfib_lib_pre_x in HB. cbn [u_fx u_ly u_S u_W u_regs u_mem u_md u_p u_n u_pl u_M] in *.
destruct HB as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs & Hnev & Hbb & Haro & Hsink & Hfd & Hfs & Hmeta & Hmo).
pose proof HAFN as (HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstkv : LLVMF_STK = 32768) by reflexivity.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
assert (Hp : 4096 <= p /\ p + n <= 140737479966720).
{ destruct Hpn as [(-> & ->) | (Hn & Hin)]; [unfold A_EMPTY; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hb1 & Hb3 & _).
  pose proof (req_size_pos n ltac:(lia)) as Hrq. lia. }
assert (Hpc : n = 0 \/ p + n <= alloc_ceiling).
{ destruct Hpn as [(-> & _) | (Hn & Hin)]; [left; reflexivity|]. right.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hb1 & Hb3 & _).
  pose proof (req_size_pos n ltac:(lia)) as Hrq. lia. }
destruct HOH as (ly' & S' & regs' & mem' & md' & off & mm & vs & -> & HC & HM & R8 & R9 & R18 & Hmm & R22 & R23 & R24
  & R25 & R26 & Hoff & HRES).
pose proof HC as (HJ & Hfrs' & Hsp' & Hgp' & Htp' & H27' & Hsv' & Hperm').
unfold u_sp1, u_sp0, U_FRAME in *. cbn [u_regs u_n u_p] in *.
assert (R2 : getr regs' 2 = w64 (spZ regs - 144)) by (unfold w64; rewrite <- Hsp'; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRS & _).
assert (Hinb : 0 < n -> In (p, n) (ablocks B ly' S')).
{ intros Hn0. destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia|]. exact (Permutation_in _ (Permutation_sym Hperm') Hin). }
assert (Hin0 : 0 < n -> In (p, n) (ablocks B ly S)).
{ intros Hn0. destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia | exact Hin]. }
set (v0 := ta_byte pl off). set (v1 := ta_byte pl (off + 1)). set (v2 := ta_byte pl (off + 2)).
set (v3 := ta_byte pl (off + 3)). set (v4 := ta_byte pl (off + 4)).
pose proof (ta_byte_range pl off) as Hv0. pose proof (ta_byte_range pl (off + 1)) as Hv1.
pose proof (ta_byte_range pl (off + 2)) as Hv2. pose proof (ta_byte_range pl (off + 3)) as Hv3.
pose proof (ta_byte_range pl (off + 4)) as Hv4. fold v0 v1 v2 v3 v4 in Hv0, Hv1, Hv2, Hv3, Hv4.
pose proof (ta_entry (fx := fx) W' regs' mem' (spZ regs - 144) n p off v0 v1 v2 v3 v4 R2 ltac:(lia)
  ltac:(rewrite Zminus_mod, Hsp16; reflexivity) ltac:(intros a Ha; apply HPRS; lia)
  R8 Hn26 R9 (proj1 Hp) ltac:(lia) R22 R24 Hoff Hv0 Hv1 Hv2 Hv3 Hv4) as HS.
set (E0 := ETA regs' (p + off) v0 v1 v2 v3 v4) in HS.
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs' r)
  by (intros k r Hk; unfold E0, ETA; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 6)%nat -> ew E0 (32 + j) = nth j (ta_extra (p + off) v0 v1 v2 v3 v4) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, ETA; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [nth ta_extra Nat.add] in E32, E33, E34, E35, E36, E37.
assert (E2 : ew E0 2 = w64 (spZ regs - 144)) by (rewrite (ER 2%nat 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E0 2) = spZ regs - 144) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
assert (E8 : ew E0 8 = w64 n) by (rewrite (ER 8%nat 8%bv eq_refl); exact R8).
assert (E22 : ew E0 22 = w64 SHADOW_OFF) by (rewrite (ER 22%nat 22%bv eq_refl); exact R22).
assert (E24 : ew E0 24 = w64 off) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
assert (U32 : bv_unsigned (ew E0 32) = p + off) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs (SOff 22 0) [] E0 (mrestrict (w_H W') mem')) by constructor.
assert (HEI : img_env (@pa_val _ uci_listing PI_uci) A_LIM E0) by (unfold E0, ETA; apply Eimg_env).
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 + 8 <= a < spZ regs - 144 + 12) ->
  aview segs (w_H W') mem' a = aview segs (w_H W') mem' a) by reflexivity.
pose proof (fun Ex ss ms md'' kk len e0 e1 e2 e3 c0 c1 c2 c3 =>
  ta_close (fx := fx) B MT XL ly S W regs mem md p n pl M i ly' S' W' regs' mem' md' off mm vs (p + off) v0 v1 v2 v3 v4
    Ex ss ms md'' kk len e0 e1 e2 e3 c0 c1 c2 c3 HC HM R8 R9 R18 Hmm R22 R23 R24 R25 R26 (proj1 Hoff) HRES
    ltac:(unfold u_sp1, u_sp0, U_FRAME; cbn [u_regs]; lia)) as FIN.
pose proof (paj_run (fx := fx) (SK := AE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx) (SK := AE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUNTO.
pose proof (@paj_branch fx rc uci_listing PI_uci) as BR.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ uci_listing PI_uci) Wx
    (mkCfg (mkst regs' (Z_to_bv 64 (@pa_val _ uci_listing PI_uci A_TEXT + U_OH)) mem'
      (seg_rom (@pa_segs _ uci_listing PI_uci))) md') Q) end.
(* +0xa8 .. +0xb4: sw zero, 8(sp); a1 = sp + 8; a2 = 4; the first `bgeu s8, s0`. *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 304; [ta_awr U2|]. ta_kupd KR U2. ta_md.
(* The comb: byte j guarded by `bgeu s8 + j, s0`. *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ ta_br_geu 0 E24 E8 off n. ta_past FIN RUN RUNTO BR HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off E33 E34 E35 E36 E37. }
ta_br_geu 0 E24 E8 off n.
ta_addb 0%nat off HS HJ U32 U2 E33 Hv0 Hin0 Hinb Hgarr Hlen ly S W mem md ly' S' W' p n pl off.
ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ ta_br_geu 1 E24 E8 off n. ta_past FIN RUN RUNTO BR HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off E33 E34 E35 E36 E37. }
ta_br_geu 1 E24 E8 off n.
ta_addb 1%nat (off + 1) HS HJ U32 U2 E34 Hv1 Hin0 Hinb Hgarr Hlen ly S W mem md ly' S' W' p n pl off.
ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ ta_br_geu 2 E24 E8 off n. ta_past FIN RUN RUNTO BR HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off E33 E34 E35 E36 E37. }
ta_br_geu 2 E24 E8 off n.
ta_addb 2%nat (off + 2) HS HJ U32 U2 E35 Hv2 Hin0 Hinb Hgarr Hlen ly S W mem md ly' S' W' p n pl off.
ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ ta_br_geu 3 E24 E8 off n. ta_past FIN RUN RUNTO BR HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off E33 E34 E35 E36 E37. }
ta_br_geu 3 E24 E8 off n.
ta_addb 3%nat (off + 3) HS HJ U32 U2 E36 Hv3 Hin0 Hinb Hgarr Hlen ly S W mem md ly' S' W' p n pl off.
ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off.
(* the length byte *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ ta_br_geu 4 E24 E8 off n. ta_past FIN RUN RUNTO BR HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off E33 E34 E35 E36 E37. }
ta_br_geu 4 E24 E8 off n.
ta_addb 4%nat (off + 4) HS HJ U32 U2 E37 Hv4 Hin0 Hinb Hgarr Hlen ly S W mem md ly' S' W' p n pl off.
ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off.
(* all five read: `bltu s3, a0` with s3 = n - (off + 5), a0 = the length byte *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ rewrite branch_ltu_U, (ta_U_rest _ 8 24 (-5) n off), (U_atom _ 37 v4) in Hc
    by (first [ta_ew E8 | ta_ew E24 | ta_ew E37 | lia]).
  apply Z.ltb_lt in Hc.
  ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off.
  ta_fin FIN HJ KR HS E33 E34 E35 E36 E37 ltac:(ta_s3_get HS; rewrite denot_lit_U;
    rewrite (ta_U_rest _ 8 24 (-5) n off) by (first [ta_ew E8 | ta_ew E24 | lia]); reflexivity). }
rewrite branch_ltu_U, (ta_U_rest _ 8 24 (-5) n off), (U_atom _ 37 v4) in Hc
  by (first [ta_ew E8 | ta_ew E24 | ta_ew E37 | lia]).
apply Z.ltb_ge in Hc.
ta_step RUNTO HS HJ SHOK KR U2 LAWS Hinb E22 E32 p n off.
ta_fin FIN HJ KR HS E33 E34 E35 E36 E37 ltac:(ta_s3_get HS; eapply ta_dv_atom; [ta_ew E37 | lia]).
Qed.
End sg.
