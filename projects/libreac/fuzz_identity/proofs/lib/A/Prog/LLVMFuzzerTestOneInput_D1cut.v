(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its module paths and module names changed; 601 of its 728 lines of code are new or changed and 5938 lines of the source are left out. *)
(* Segment D1 of LLVMFuzzerTestOneInput's ASan walk (0x80b20..0x80d04, seg_D1 of LLVMFuzzerTestOneInput_inv.v):
   the cut of the segment into its ten phases, so that each phase is proved in its own file.

   The phases (offsets from BASE = 0x8070c; each ends at the return address of its last call):
     Ph1  0x414 -> 0x4c0  the record header (fuzz_u16, fuzz_u8, fuzz_take: three checked input loads, the address
                          bias of pick_addr, the length), then malloc(k) for the payload copy pl (0x80bc8)
     Ph2  0x4c0 -> 0x4e8  the NULL check of pl, mf+144 := n - body, memcpy(pl, body, k) when k > 0 (0x80bf0)
     Ph3  0x4e8 -> 0x510  `before`'s shadow is unpoisoned (5 cells, 0x80bf4..0x80c04), memcpy(before, id, 38) (0x80c18)
     Ph4  0x510 -> 0x524  reac_identity_ingest(&id, addr, pl, k) (0x80c2c)
     Ph5  0x524 -> 0x538  the result is >= 0 (0x80c30), malloc(k + 1) for the guard copy g (0x80c40)
     Ph6  0x538 -> 0x558  the NULL check of g, memcpy(g, pl, k) when k > 0 (0x80c60)
     Ph7  0x558 -> 0x5ac  mf+152 := pl, mf+160 := i, the checked store g[k] := 'Z' (0x80c6c..0x80c8c, slow shadow path
                          0x8142c), mf+136 := body, `again`'s shadow is unpoisoned (0x80c90..0x80ca0), memcpy(again,
                          before, 38) (0x80cb4)
     Ph8  0x5ac -> 0x5c0  reac_identity_ingest(&again, addr, g, k) (0x80cc8)
     Ph9  0x5c0 -> 0x5cc  free(g) (0x80cd4)
     Ph10 0x5cc -> 0x5f8  the two results and the first three bytes of the two identities agree (inv_D1_end)
   This file holds the predicates the phases share (D1ctx: the segment's start, inv_rec's state; D1S: the running
   state; RC / RCb and P1..P9: what each phase hands to the next), the facts every phase uses, Ph1's malloc step,
   and the statements d1_ph2_stmt .. d1_ph9_stmt. Ph1, Ph10 and seg_D1_holds are LLVMFuzzerTestOneInput_D1.v; the
   other phases are proved in LLVMFuzzerTestOneInput_D1p23.v, _D1p48.v, _D1p56.v, _D1p79.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g YK0w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv reac_identity_ingest.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the shadow arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model of the record header (SlotModel.v), as the machine computes it ------------------------ *)
Module D1Model.
Import SlotModel RcIdentModel.
Lemma inb_beyond : forall inp j, nlen inp <= j -> inb inp j = 0.
Proof.
intros inp j H. unfold inb, nthb, nlen in *. rewrite nth_overflow by lia. reflexivity.
Qed.
Lemma d1_hdr : forall inp c, 0 <= c <= nlen inp ->
  h_h inp c = Z.min (nlen inp - c) 3 /\ h_body inp c = c + Z.min (nlen inp - c) 3 /\
  h_k inp c = (if nlen inp - c <? 3 then 0 else Z.min (inb inp (c + 2)) (nlen inp - c - 3)) /\
  h_raw inp c = (if nlen inp - c =? 0 then 0 else if nlen inp - c =? 1 then inb inp c
                 else inb inp c + 256 * inb inp (c + 1)).
Proof.
intros inp c Hc. unfold h_k, h_Lp, h_body, h_h, h_left, h_raw, h_lo, h_hi, h_w.
split; [reflexivity|]. split; [reflexivity|].
split.
- pose proof (inb_range inp (c + 2)). destruct (Z.ltb_spec (nlen inp - c) 3); lia.
- destruct (Z.eqb_spec (nlen inp - c) 0).
  + rewrite !inb_beyond by lia. lia.
  + destruct (Z.eqb_spec (nlen inp - c) 1); [|reflexivity].
    rewrite (inb_beyond inp (c + 1)) by lia. lia.
Qed.
Lemma d1_pick : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 ->
  pick (lo + 256 * hi) = (if hi / 64 =? 0 then ADDR_FIRMWARE else if hi / 64 =? 1 then ADDR_REAC_VERSION
                          else if hi / 64 =? 2 then ADDR_MODEL_NAME else lo + 256 * hi).
Proof.
intros lo hi Hlo Hhi. unfold pick.
replace ((lo + 256 * hi) / 16384) with (hi / 64); [reflexivity|].
apply Z.div_unique with (r := lo + 256 * (hi mod 64)); [lia|].
pose proof (Z.div_mod hi 64 ltac:(lia)). pose proof (Z.mod_pos_bound hi 64 ltac:(lia)). lia.
Qed.
Lemma d1_pick_lo : forall lo, 0 <= lo < 256 -> pick lo = ADDR_FIRMWARE.
Proof. intros lo H. unfold pick. rewrite Z.div_small by lia. reflexivity. Qed.
Lemma d1_pick_range : forall raw, 0 <= raw < 65536 -> 0 <= pick raw < 65536.
Proof.
intros raw H. unfold pick, ADDR_FIRMWARE, ADDR_REAC_VERSION, ADDR_MODEL_NAME.
destruct (raw / 16384 =? 0); [lia|]. destruct (raw / 16384 =? 1); [lia|]. destruct (raw / 16384 =? 2); lia.
Qed.
Lemma d1_raw_range : forall inp c, 0 <= h_raw inp c < 65536.
Proof.
intros inp c. unfold h_raw, h_lo, h_hi. pose proof (inb_range inp c). pose proof (inb_range inp (c + 1)). lia.
Qed.
Lemma d1_addr_range : forall inp i, 0 <= rec_addr inp i < 65536.
Proof. intros inp i. unfold rec_addr, rec_raw. apply d1_pick_range. apply d1_raw_range. Qed.
(* The record is accepted with r in {0, 1}, and the identity after it is ING's. *)
Lemma d1_ingest_ret : forall inp i id p,
  id <> 0 -> (rec_k inp i <> 0 -> p <> 0) ->
  reac_identity_ingest_c.ingest_ret id (rec_addr inp i) p (rec_k inp i) (rec_id inp i) (rec_pl inp i) = rec_r inp i.
Proof.
intros inp i id p Hid Hp. unfold reac_identity_ingest_c.ingest_ret, reac_identity_ingest_c.ingest_refused.
destruct (Z.eqb_spec id 0) as [E|_]; [lia|]. cbn [orb].
destruct (Z.eqb_spec (rec_k inp i) 0) as [E|E]; cbn [negb andb]; [reflexivity|].
destruct (Z.eqb_spec p 0) as [E2|_]; [exfalso; exact (Hp E E2) | reflexivity].
Qed.
Lemma d1_ingest_ok : forall inp i id p,
  id <> 0 -> (rec_k inp i <> 0 -> p <> 0) ->
  reac_identity_ingest_c.ingest_refused id p (rec_k inp i) = false.
Proof.
intros inp i id p Hid Hp. unfold reac_identity_ingest_c.ingest_refused.
destruct (Z.eqb_spec id 0) as [E|_]; [lia|]. cbn [orb].
destruct (Z.eqb_spec (rec_k inp i) 0) as [E|E]; cbn [negb andb]; [reflexivity|].
destruct (Z.eqb_spec p 0) as [E2|_]; [exfalso; exact (Hp E E2) | reflexivity].
Qed.
End D1Model.

(* ---- small facts ---------------------------------------------------------------------------------------------- *)
Lemma d1_den_eq : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof.
intros E e v H Hv. apply bv_eq. rewrite Z_to_bv_unsigned. unfold U in H. rewrite H. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma d1_branch_lt : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts, U in *. rewrite !bv_signed_small by exact Ha || exact Hb.
reflexivity.
Qed.
Lemma d1_branch_ge : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof.
intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts, U in *. rewrite !bv_signed_small by exact Ha || exact Hb.
reflexivity.
Qed.
Lemma d1_zcanon_small : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma d1_U_srl6 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_SRL (SOff n 0) (SLit 6)) = v / 64.
Proof.
intros E n v Hn Hv. rewrite U_SAlu, (U_atom E n v Hn) by lia. rewrite U_lit by lia. cbn [zalu_raw].
change (Z.land 6 63) with 6. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64.
apply d1_zcanon_small. split; [apply Z.div_pos; lia | apply (Z.le_lt_trans _ v); [apply Z.div_le_upper_bound; lia | lia]].
Qed.
Lemma d1_U_raw : forall E nl nh lo hi, ew E nl = Z_to_bv 64 lo -> ew E nh = Z_to_bv 64 hi ->
  0 <= lo < 256 -> 0 <= hi < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff nh 0) (SLit 8)) (SOff nl 0)) = lo + 256 * hi.
Proof.
intros E nl nh lo hi Hl Hh Hlo Hhi. rewrite !U_SAlu, (U_atom E nl lo Hl), (U_atom E nh hi Hh) by lia. rewrite U_lit by lia.
cbn [zalu_raw]. change (Z.land 8 63) with 8.
assert (Hs : Z.shiftl hi 8 = hi * 256) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
rewrite (d1_zcanon_small (Z.shiftl hi 8)) by lia. rewrite Z.lor_comm, YK0w.lor_shiftl8 by lia.
apply d1_zcanon_small. lia.
Qed.


(* The shadow base and span of the token engine (identity's SHADOW_OFF). *)
Definition d1_SB : Z := 0x7fff8000.
Definition d1_Bx : sv := SOff 32 0.
Definition d1_Bspan : Z * Z := (d1_SB, d1_SB + 2 ^ 44 - 1).

Lemma d1_frame_ro : forall segs E (rs : smem) (m m' : word -> option byte) H a,
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' ->
  aview segs H m' a = aview segs H m a.
Proof.
intros segs E rs m m' H a Hro HF. apply (aview_eq_of segs). unfold mrestrict. rewrite HF; [reflexivity|].
intros (r & Hin & Ha). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma d1_U_off : forall E n x v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  U E (SOff n x) = v + x.
Proof. intros E n x v H Hv Hx. rewrite U_SOff, H, unsigned_lit_small by exact Hv. apply d1_zcanon_small. exact Hx. Qed.
Lemma d1_reg_val : forall E e (regs : bvmap 5 word) (r : bv 5) v,
  getr regs r = sv_denot E e -> U E e = v -> 0 <= v < 2 ^ 64 -> getr regs r = w64 v.
Proof. intros E e regs r v H HU Hv. rewrite H. apply d1_den_eq; assumption. Qed.
Ltac d1_ew := cbn [ew ewset extK Nat.eqb]; first [assumption | eassumption].
Ltac d1_hcZ Hc := first [ apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc | apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc
  | apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc
  | apply negb_true_iff, Z.eqb_neq in Hc | apply negb_false_iff, Z.eqb_eq in Hc ].
(* A branch condition of the header, as a fact about hi / 64 or w. *)
(* After a run whose regions are all read-only: memory as it was (the run's frame_of has no window). *)
Ltac d1_keep_ro :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m0) (mrestrict (w_H ?W) ?m1),
    KP : forall a, 0 <= a < 2 ^ 64 -> aview ?sg (w_H ?W) ?m0 a = aview ?sg (w_H ?W) ?mm a |- _ =>
    let K2 := fresh "KP" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview sg (w_H W) m1 a = aview sg (w_H W) mm a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; etransitivity; [|exact (KP a Ha)];
          apply (kept_of_frame Ex rs (w_H W) m0 m1 (fun _ => False) HFr);
          [ let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
            let Hin := fresh "Hin" in let Hr := fresh "Hr" in
            intros bb wl wh aa Hin Hr; vm_compute in Hin;
            repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia |]);
            destruct Hin
          | exact Ha | intros [] ]);
    clear KP; rename K2 into KP
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac d1_prraw HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
(* What this segment takes, each with the name and type the contract's Section gives it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
(* The allocator call traces (LLVMFuzzerTestOneInput.v, the contract's text). *)
Hypothesis HUMM : forall c, In c (LLVMF_MALLOC_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).

(* ---- the segment's start and its running state -------------------------------------------------------------- *)
(* The model's values of the record (SlotModel.v). *)
Definition D1k (g : ectx) (i : nat) : Z := SlotModel.rec_k (e_pl g) i.
Definition D1body (g : ectx) (i : nat) : Z := SlotModel.rec_body (e_pl g) i.
Definition D1addr (g : ectx) (i : nat) : Z := SlotModel.rec_addr (e_pl g) i.
(* inv_rec's state. *)
Definition D1ctx (g : ectx) (pos mf : Z) (i : nat) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat i) /\
  frames S2 = [(4, pos)] /\ 0 <= 4 * Z.of_nat i <= EV_LLVMF /\
  mo_le MT (e_S g) S2 (4 * Z.of_nat i * (mo_malloc MT 256 + mo_free MT)) /\
  mo_ok MT S2 ((EV_LLVMF - 4 * Z.of_nat i) * (mo_malloc MT 256 + mo_free MT)) /\
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 /\
  (i < m_nrec g)%nat /\ getr regs2 20 = w64 (Z.of_nat i) /\
  getr regs2 21 = w64 6 /\ getr regs2 24 = w64 (SFa g pos + V_before) /\
  rec_live B g pos mf i ly2 S2 W2 regs2 mem2.
(* The bytes the segment may change before the first ingest: the callees' stack below mf, the machine-frame slots
   136..167, `before`, `again` and their shadow cells. After it, `id` too. *)
Definition WR0 (g : ectx) (pos mf : Z) (a : Z) : Prop :=
  (mf - ASTACK <= a < mf) \/ (mf + 136 <= a < mf + 168) \/
  (SFa g pos + V_before <= a < SFa g pos + V_before + N_before) \/
  (SFa g pos + V_again <= a < SFa g pos + V_again + N_again) \/
  (shadow_addr (SFa g pos) + 4 <= a < shadow_addr (SFa g pos) + 9) \/
  (shadow_addr (SFa g pos) + 14 <= a < shadow_addr (SFa g pos) + 19).
Definition WR1 (g : ectx) (pos mf : Z) (a : Z) : Prop :=
  WR0 g pos mf a \/ (SFa g pos + V_id <= a < SFa g pos + V_id + N_id).
(* The running state at slot pc: the journal from the entry with kk more events than at the start, the frame,
   the heap blocks hs allocated since the start, the meter spent since the start, and everything of the machine
   stack, the frame and the frame's shadow outside WR as at the start. P says the rest. *)
Definition D1S (g : ectx) (pos mf : Z) (i : nat) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 : word -> option byte) (kk pc spent : Z) (hs : list (Z * Z)) (WR : Z -> Prop)
  (P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Prop)
  : world SEGS -> config -> Prop :=
  fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
    c3 = cfg_at SEGS pc regs3 mem3 md3 /\
    ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
      ly3 S3 W3 mem3 md3 (4 * Z.of_nat i + kk) /\
    frames S3 = [(4, pos)] /\
    Permutation (ablocks B ly3 S3) (hs ++ ablocks B ly2 S2) /\ Forall (fun h => 4096 <= fst h) hs /\
    mo_le MT S2 S3 spent /\
    (forall a, 0 <= a < 2 ^ 64 ->
       (alloc_ceiling <= a \/ SFa g pos <= a < SFa g pos + 1024 \/
        shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
       ~ WR a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) /\
    P ly3 S3 W3 regs3 mem3.
(* The callee-saved registers no phase changes. *)
Definition RC (g : ectx) (pos mf : Z) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 mf /\ getr regs 9 = w64 mf /\ getr regs 8 = w64 (e_sp0 g) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 19 = w64 (shadow_addr (SFa g pos)) /\ getr regs 20 = w64 (Z.of_nat i) /\
  getr regs 21 = w64 6 /\ getr regs 24 = w64 (SFa g pos + V_before).
(* After Ph1 (0x80bcc): the header is parsed and pl is the payload copy's block. *)
Definition P1 (g : ectx) (pos mf : Z) (i : nat) (pl : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  RC g pos mf i regs3 /\ getr regs3 10 = w64 pl /\
  getr regs3 22 = w64 (D1k g i) /\ getr regs3 27 = w64 (D1addr g i) /\
  getr regs3 26 = w64 (e_p g + D1body g i) /\ getr regs3 18 = w64 (e_n g - D1body g i).


(* The callee-saved registers Ph7..Ph10 keep (Ph7 reuses s4 for &again, Ph9 s5 for the second result). *)
Definition RCb (g : ectx) (pos mf : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 mf /\ getr regs 9 = w64 mf /\ getr regs 8 = w64 (e_sp0 g) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 19 = w64 (shadow_addr (SFa g pos)) /\ getr regs 24 = w64 (SFa g pos + V_before).
(* After Ph2 (0x80bf4): mf+144 holds the length left after the header, pl holds the payload. *)
Definition P2 (g : ectx) (pos mf : Z) (i : nat) (pl : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  RC g pos mf i regs3 /\ getr regs3 25 = w64 pl /\
  getr regs3 22 = w64 (D1k g i) /\ getr regs3 27 = w64 (D1addr g i) /\
  getr regs3 26 = w64 (e_p g + D1body g i) /\ getr regs3 18 = w64 (e_n g - D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 144) 8 (e_n g - D1body g i) /\
  bytes_at8 W3 mem3 pl (SlotModel.rec_pl (e_pl g) i).
(* After Ph3 (0x80c1c): `before` is unpoisoned and holds the identity before the record; s2 = &id. *)
Definition P3 (g : ectx) (pos mf : Z) (i : nat) (pl : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  RC g pos mf i regs3 /\ getr regs3 25 = w64 pl /\
  getr regs3 22 = w64 (D1k g i) /\ getr regs3 27 = w64 (D1addr g i) /\
  getr regs3 26 = w64 (e_p g + D1body g i) /\ getr regs3 18 = w64 (SFa g pos + V_id) /\
  val_mem SEGS (rd W3 mem3) (mf + 144) 8 (e_n g - D1body g i) /\
  bytes_at8 W3 mem3 pl (SlotModel.rec_pl (e_pl g) i) /\
  sh_blk W3 mem3 (SFa g pos + V_before) N_before /\ bytes_at8 W3 mem3 (SFa g pos + V_before) (m_id g i).
(* After Ph4 (0x80c30): the first ingest ran; a0 = its result, id = the identity after the record. *)
Definition P4 (g : ectx) (pos mf : Z) (i : nat) (pl : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  RC g pos mf i regs3 /\ getr regs3 10 = w64 (SlotModel.rec_r (e_pl g) i) /\ getr regs3 25 = w64 pl /\
  getr regs3 22 = w64 (D1k g i) /\ getr regs3 27 = w64 (D1addr g i) /\
  getr regs3 26 = w64 (e_p g + D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 144) 8 (e_n g - D1body g i) /\
  bytes_at8 W3 mem3 pl (SlotModel.rec_pl (e_pl g) i) /\
  sh_blk W3 mem3 (SFa g pos + V_before) N_before /\ bytes_at8 W3 mem3 (SFa g pos + V_before) (m_id g i) /\
  bytes_at8 W3 mem3 (SFa g pos + V_id) (m_id g (S i)).
(* After Ph5 (0x80c44): s7 = the first result, a0 = gb, the guard copy's block. *)
Definition P5 (g : ectx) (pos mf : Z) (i : nat) (pl gb : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  RC g pos mf i regs3 /\ getr regs3 10 = w64 gb /\ getr regs3 23 = w64 (SlotModel.rec_r (e_pl g) i) /\
  getr regs3 25 = w64 pl /\ getr regs3 22 = w64 (D1k g i) /\ getr regs3 27 = w64 (D1addr g i) /\
  getr regs3 26 = w64 (e_p g + D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 144) 8 (e_n g - D1body g i) /\
  bytes_at8 W3 mem3 pl (SlotModel.rec_pl (e_pl g) i) /\
  sh_blk W3 mem3 (SFa g pos + V_before) N_before /\ bytes_at8 W3 mem3 (SFa g pos + V_before) (m_id g i) /\
  bytes_at8 W3 mem3 (SFa g pos + V_id) (m_id g (S i)).
(* After Ph6 (0x80c64): s2 = gb, and gb holds the payload. *)
Definition P6 (g : ectx) (pos mf : Z) (i : nat) (pl gb : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  RC g pos mf i regs3 /\ getr regs3 18 = w64 gb /\ getr regs3 23 = w64 (SlotModel.rec_r (e_pl g) i) /\
  getr regs3 25 = w64 pl /\ getr regs3 22 = w64 (D1k g i) /\ getr regs3 27 = w64 (D1addr g i) /\
  getr regs3 26 = w64 (e_p g + D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 144) 8 (e_n g - D1body g i) /\
  bytes_at8 W3 mem3 pl (SlotModel.rec_pl (e_pl g) i) /\ bytes_at8 W3 mem3 gb (SlotModel.rec_pl (e_pl g) i) /\
  sh_blk W3 mem3 (SFa g pos + V_before) N_before /\ bytes_at8 W3 mem3 (SFa g pos + V_before) (m_id g i) /\
  bytes_at8 W3 mem3 (SFa g pos + V_id) (m_id g (S i)).
(* After Ph7 (0x80cb8): mf+136/152/160 are stored, `again` is unpoisoned and holds `before`; s4 = &again. *)
Definition P7 (g : ectx) (pos mf : Z) (i : nat) (pl gb : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  RCb g pos mf regs3 /\ getr regs3 20 = w64 (SFa g pos + V_again) /\ getr regs3 18 = w64 gb /\
  getr regs3 23 = w64 (SlotModel.rec_r (e_pl g) i) /\
  getr regs3 25 = w64 pl /\ getr regs3 22 = w64 (D1k g i) /\ getr regs3 27 = w64 (D1addr g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 136) 8 (e_p g + D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 144) 8 (e_n g - D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 152) 8 pl /\ val_mem SEGS (rd W3 mem3) (mf + 160) 8 (Z.of_nat i) /\
  bytes_at8 W3 mem3 pl (SlotModel.rec_pl (e_pl g) i) /\ bytes_at8 W3 mem3 gb (SlotModel.rec_pl (e_pl g) i) /\
  sh_blk W3 mem3 (SFa g pos + V_before) N_before /\ bytes_at8 W3 mem3 (SFa g pos + V_before) (m_id g i) /\
  sh_blk W3 mem3 (SFa g pos + V_again) N_again /\ bytes_at8 W3 mem3 (SFa g pos + V_again) (m_id g i) /\
  bytes_at8 W3 mem3 (SFa g pos + V_id) (m_id g (S i)).
(* After Ph8 (0x80ccc): the second ingest ran on `again`; a0 = its result. *)
Definition P8 (g : ectx) (pos mf : Z) (i : nat) (pl gb : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  RCb g pos mf regs3 /\ getr regs3 20 = w64 (SFa g pos + V_again) /\ getr regs3 18 = w64 gb /\
  getr regs3 10 = w64 (SlotModel.rec_r (e_pl g) i) /\ getr regs3 23 = w64 (SlotModel.rec_r (e_pl g) i) /\
  getr regs3 25 = w64 pl /\ getr regs3 22 = w64 (D1k g i) /\ getr regs3 27 = w64 (D1addr g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 136) 8 (e_p g + D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 144) 8 (e_n g - D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 152) 8 pl /\ val_mem SEGS (rd W3 mem3) (mf + 160) 8 (Z.of_nat i) /\
  bytes_at8 W3 mem3 pl (SlotModel.rec_pl (e_pl g) i) /\ bytes_at8 W3 mem3 gb (SlotModel.rec_pl (e_pl g) i) /\
  sh_blk W3 mem3 (SFa g pos + V_before) N_before /\ bytes_at8 W3 mem3 (SFa g pos + V_before) (m_id g i) /\
  sh_blk W3 mem3 (SFa g pos + V_again) N_again /\ bytes_at8 W3 mem3 (SFa g pos + V_again) (m_id g (S i)) /\
  bytes_at8 W3 mem3 (SFa g pos + V_id) (m_id g (S i)).
(* After Ph9 (0x80cd8): gb is freed; s5 = the second result. *)
Definition P9 (g : ectx) (pos mf : Z) (i : nat) (pl : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  RCb g pos mf regs3 /\ getr regs3 20 = w64 (SFa g pos + V_again) /\
  getr regs3 21 = w64 (SlotModel.rec_r (e_pl g) i) /\ getr regs3 23 = w64 (SlotModel.rec_r (e_pl g) i) /\
  getr regs3 25 = w64 pl /\ getr regs3 22 = w64 (D1k g i) /\ getr regs3 27 = w64 (D1addr g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 136) 8 (e_p g + D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 144) 8 (e_n g - D1body g i) /\
  val_mem SEGS (rd W3 mem3) (mf + 152) 8 pl /\ val_mem SEGS (rd W3 mem3) (mf + 160) 8 (Z.of_nat i) /\
  bytes_at8 W3 mem3 pl (SlotModel.rec_pl (e_pl g) i) /\
  sh_blk W3 mem3 (SFa g pos + V_before) N_before /\ bytes_at8 W3 mem3 (SFa g pos + V_before) (m_id g i) /\
  sh_blk W3 mem3 (SFa g pos + V_again) N_again /\ bytes_at8 W3 mem3 (SFa g pos + V_again) (m_id g (S i)) /\
  bytes_at8 W3 mem3 (SFa g pos + V_id) (m_id g (S i)).

Ltac d1_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; unfold acallee_saved; lia.
Lemma d1_presv : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma d1_RC_pres : forall g pos mf i regs regs', aregs_preserved regs regs' -> RC g pos mf i regs -> RC g pos mf i regs'.
Proof.
intros g pos mf i regs regs' HP (R2 & R9 & R8 & R3 & R4 & R19 & R20 & R21 & R24).
unfold RC. repeat split; (rewrite d1_presv with (regs := regs); [assumption | exact HP | d1_cs]).
Qed.

(* The numbers of the start state every phase uses. *)
Lemma d1_nums : forall g pos mf i ly2 S2 W2 regs2 mem2 md2,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  alloc_ceiling + ASTACK <= mf /\ e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\ mf mod 32 = 0 /\
  e_sp0 g mod 16 = 0 /\ e_sp0 g <= 2 ^ 47 /\ e_sp0 g - LLVMF_STK <= mf - ASTACK /\
  (4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ SFa g pos mod 64 = 0 /\ in_app (SFa g pos) 1024 /\
   frame_addr ly2 4 pos = SFa g pos) /\
  (0 < e_n g < 2 ^ 26 /\ In (e_p g, e_n g) (ablocks B ly2 S2) /\ In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)) /\
   4096 <= e_p g /\ e_p g + req_size (e_n g) <= alloc_ceiling /\ in_app (e_p g) (req_size (e_n g)) /\
   SlotModel.nlen (e_pl g) = e_n g) /\
  Z.of_nat i < 64 /\ 0 <= m_cur g i <= e_n g.
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 HC.
destruct HC as (HJ & Hfrs & Hk & MLE & MOK & HEC & Hi & R20 & R21 & R24 & HRL).
destruct HEC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HRL as (V112 & Hfix & Hcur & Hid & Hhw & Hbl & Hmid & Hmag).
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. change (fs_frame_bytes 4) with 1024 in HSF1, HSFapp.
assert (Hnr : (0 < m_nrec g)%nat) by lia.
assert (Hn : 0 < e_n g).
{ unfold m_nrec, SlotModel.nrecn, SlotModel.nrec, SlotModel.inb in Hnr.
  destruct (e_pl g) as [|b l] eqn:El; [vm_compute in Hnr; lia|]. rewrite Hlen. cbn [length]. lia. }
destruct Hinp as [[Hn0 _] | [Hn26 Hine]]; [lia|].
assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hine. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hine2) as (_ & Hp4096 & Hpce & Hpapp & _).
assert (Hi64 : Z.of_nat i < 64).
{ pose proof (SlotModel.nrec_range (e_pl g)). unfold m_nrec, SlotModel.nrecn in Hi. lia. }
destruct Hcur as (_ & _ & Hcur).
split; [clear - Hmfb Hceil Hslo HSTK' Has; lia|]. split; [exact Hmfb|]. split; [exact Hmf32|].
split; [exact Hsp0al|]. split; [clear - Hshi H47; lia|].
split; [clear - Has HSTK' Hmfb; lia|].
split; [exact (conj HSF0 (conj HSF1 (conj HSF64 (conj HSFapp EFa))))|].
split; [|split; [exact Hi64 | exact Hcur]].
refine (conj (conj Hn (proj2 Hn26)) (conj Hine2 (conj Hine (conj Hp4096 (conj Hpce (conj Hpapp _)))))).
unfold SlotModel.nlen. rewrite Hlen. reflexivity.
Qed.

(* The call chain at a call made with sp = mf: the entry's frame record at sp0 on top of the entry's chain
   (as segment D6 builds it), or no record when sp0 lies within 16 bytes of the stack top. *)
Lemma d1_chain : forall g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 mem3 md3 kk (regsT : bvmap 5 word),
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly3 S3 W3 mem3 md3 kk ->
  (forall a, mf <= a < e_sp0 g -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  spZ regsT = mf -> s0Z regsT = e_sp0 g -> 4096 <= raZ regsT ->
  exists ch, chain_pre ly3 (aview SEGS (w_H W3) mem3) regsT ch /\
    (ch = [] \/ ch = [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))]).
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 mem3 md3 kk regsT HC HJ3 KEEP Usp Us0 Ura4.
pose proof (d1_nums g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & _ & Hsp0al & H47 & _).
destruct HC as (HJ & _ & _ & _ & _ & HEC & _).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vra & Vs0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof HPRE as (HFN & Hraz & _).
pose proof HFN as (_ & _ & Hra4 & _ & _ & _ & _ & Hch0 & _).
pose proof HJ3 as (_ & Hly3 & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & Hstk0 & Hceil & Hslo & Hshi & H47s & _ & Htop0 & Htop1).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof asan_consts as (C1 & _).
set (sp0 := e_sp0 g) in *.
change (spZ (e_regs g)) with sp0 in Hch0.
assert (Hach : achain ly3 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
{ apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
destruct (Z_lt_le_dec sp0 (ly_top ly3 - 16)) as [Hlt | Hge].
- exists [(sp0, RA_LLVMF, s0Z (e_regs g))]. split; [|right; reflexivity].
  eapply (achain_chain_pre ly3 _ mf sp0); [| rewrite Usp; clear - Hmf0; unfold ASTACK in *; lia | exact Us0 | exact Ura4].
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  apply (achain_push ly3 _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
  + rewrite ETop. clear - Htop1 Hshi H47s. lia.
  + intros a Ha. apply F1; clear - Ha Hceil Hslo Hstk0; lia.
  + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra; lia].
    apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (sp0 - 8) (sp0 - 8) 8 RA_LLVMF); [|exact Vra].
    intros kk' Hkk. apply KEEP; clear - Hkk Hmfb; lia.
  + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
    apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (sp0 - 16) (sp0 - 16) 8 (s0Z (e_regs g))); [|exact Vs0].
    intros kk' Hkk. apply KEEP; clear - Hkk Hmfb; lia.
  + rewrite <- Hraz. exact Hra4.
  + clear - Hceil Hslo Hstk0. lia.
  + clear - Hsp0al. lia.
  + exact Hlt.
  + clear - Hmfb. lia.
- exists []. split; [|left; reflexivity].
  eapply (achain_chain_pre ly3 _ mf sp0 []); [| rewrite Usp; clear - Hmf0; unfold ASTACK in *; lia | exact Us0 | exact Ura4].
  left. split; [right; left; exact Hge | reflexivity].
Qed.
(* The allocator call traces at the entry's call sites (llvmf_univ_call / llvmf_univ_call0 of _inv.v). *)
Lemma d1_univ_malloc : forall (regsT : bvmap 5 word) o ch fp v,
  raZ regsT = BASE + o -> In o LLVMF_MALLOC_RAS -> (ch = [] \/ ch = [(fp, RA_LLVMF, v)]) ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
Proof.
intros regsT o ch fp v Hra Ho [-> | ->].
- apply (llvmf_univ_call0 B _ _ _ HUMM). rewrite Hra. unfold LLVMF_MALLOC_CTX. apply in_or_app. right.
  apply in_map_iff. exists o. split; [reflexivity | exact Ho].
- apply (llvmf_univ_call B RA_LLVMF _ _ _ _ _ HUMM). rewrite Hra. unfold LLVMF_MALLOC_CTX. apply in_or_app. left.
  apply in_map_iff. exists o. split; [reflexivity | exact Ho].
Qed.
Lemma d1_univ_free : forall (regsT : bvmap 5 word) o ch fp v,
  raZ regsT = BASE + o -> In o LLVMF_FREE_RAS -> (ch = [] \/ ch = [(fp, RA_LLVMF, v)]) ->
  In (call_trace0 (pc_free_ra0 (as_code B)) regsT ch) (as_universe B).
Proof.
intros regsT o ch fp v Hra Ho [-> | ->].
- apply (llvmf_univ_call0 B _ _ _ HUMF). rewrite Hra. unfold LLVMF_FREE_CTX. apply in_or_app. right.
  apply in_map_iff. exists o. split; [reflexivity | exact Ho].
- apply (llvmf_univ_call B RA_LLVMF _ _ _ _ _ HUMF). rewrite Hra. unfold LLVMF_FREE_CTX. apply in_or_app. left.
  apply in_map_iff. exists o. split; [reflexivity | exact Ho].
Qed.


(* A byte of the frame (4, pos) or of its shadow is in no heap block of a state that holds the frame. *)
Lemma d1_fz_not_block : forall g pos ly S W mem md b m a,
  AR SEGS B ly S W mem md -> In (4, pos) (frames S) -> frame_addr ly 4 pos = SFa g pos ->
  In (b, m) (ablocks B ly S) -> b <= a < b + req_size m ->
  ~ (SFa g pos <= a < SFa g pos + 1024 \/ shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128).
Proof.
intros g pos ly S W mem md b m a HAR Hin EFa Hb Ha Hz.
destruct (frames_bounds SEGS B LAWS ly S W mem md 4 pos HAR Hin) as (HF0 & HF1 & _).
rewrite EFa in HF0, HF1. change (fs_frame_bytes 4) with 1024 in HF1.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md b m 4 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFa in Hd. change (fs_frame_bytes 4) with 1024 in Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4096 & Hbce & Hbapp & _).
pose proof asan_consts as (C1 & _).
destruct Hz as [Hz | Hz]; [clear - Hd Ha Hz; lia|].
apply (fshadow_not_app (SFa g pos) 128 b (req_size m) a); [exact HF0 | clear - HF1 C1; lia | exact Hbapp | | exact Ha].
unfold shadow_addr, SHADOW_OFF in Hz. clear - Hz. lia.
Qed.
(* What a malloc or free call keeps of the running state's stack, frame and frame shadow. *)
Lemma d1_keep_alloc : forall g pos mf (WR : Z -> Prop) lyc Sc (Wc : world SEGS) memc (W3 : world SEGS) mem3
  (E : Z -> Prop) (W2 : world SEGS) mem2 sp0 o,
  In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = SFa g pos ->
  acall_kept SEGS B lyc Sc Wc memc W3 mem3 (sp0 + o - ASTACK) (sp0 + o) E ->
  sp0 + o = mf -> (forall a, mf - ASTACK <= a < mf -> WR a) ->
  (forall a, E a -> ~ (SFa g pos <= a < SFa g pos + 1024 \/
                       shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128)) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     (alloc_ceiling <= a \/ SFa g pos <= a < SFa g pos + 1024 \/
      shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
     ~ WR a -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     (alloc_ceiling <= a \/ SFa g pos <= a < SFa g pos + 1024 \/
      shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
     ~ WR a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
Proof.
intros g pos mf WR lyc Sc Wc memc W3 mem3 E W2 mem2 sp0 o Hin EFa HK Hmf HWR HE KEEP a Ha Hz Hn.
pose proof HK as (K1 & _ & _ & K4 & _).
rewrite <- (KEEP a Ha Hz Hn).
destruct Hz as [Hz | Hz].
- apply K1; [clear - Ha Hz; lia|]. intros Hw. apply Hn. apply HWR. clear - Hw Hmf. lia.
- apply (K4 4 pos a Hin).
  + unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4 / 8) with 128.
    change (fs_frame_bytes 4) with 1024. destruct Hz as [Hz | Hz]; [left | right]; exact Hz.
  + intros He. exact (HE a He Hz).
Qed.

(* ---- Ph1's malloc: 0x80bc8 malloc(k) -------------------------------------------------------------------------- *)
Lemma d1_malloc1 : forall g pos mf i ly2 S2 W2 regs2 mem2 md2 (regsT : bvmap 5 word) memT mdT,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 memT mdT (4 * Z.of_nat i) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) memT a = aview SEGS (w_H W2) mem2 a) ->
  RC g pos mf i regsT ->
  getr regsT 10 = w64 (D1k g i) -> getr regsT 22 = w64 (D1k g i) -> getr regsT 27 = w64 (D1addr g i) ->
  getr regsT 26 = w64 (e_p g + D1body g i) -> getr regsT 18 = w64 (e_n g - D1body g i) ->
  getr regsT 1 = Z_to_bv 64 (BASE + 0x4c0) ->
  SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) mdT)
    (fun W3 c3 => exists pl, D1S g pos mf i ly2 S2 W2 mem2 1 (BASE + 0x4c0) (mo_malloc MT (D1k g i))
                   [(pl, D1k g i)] (WR0 g pos mf) (P1 g pos mf i pl) W3 c3).
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 regsT memT mdT HC HJT KEEPT HRC R10 R22 R27 R26 R18 R1.
pose proof (d1_nums g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJ & Hfrs & Hk & MLE & MOK & HEC & Hi & _ & _ & _ & HRL).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & _ & Hnev0 & Hlive0 & _).
destruct HRL as (_ & _ & _ & _ & _ & Hbl & _ & _).
pose proof HRC as (Rsp & Rs1 & Rs0 & Rgp & Rtp & Rs3 & R20 & R21 & R24).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Has : ASTACK = 16384) by reflexivity.
set (k := D1k g i) in *.
assert (Hkr : 0 <= k <= 255) by (apply SlotModel.rec_k_range).
assert (Usp : spZ regsT = mf).
{ unfold spZ. rewrite Rsp. apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1 Has. lia. }
assert (Us0 : s0Z regsT = e_sp0 g).
{ unfold s0Z. rewrite Rs0. apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1 Has. lia. }
assert (Ura : raZ regsT = BASE + 0x4c0).
{ unfold raZ. rewrite R1. apply unsigned_lit_small. clear - HBASE. lia. }
destruct (d1_chain g pos mf i ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 memT mdT (4 * Z.of_nat i) regsT HC HJT
  ltac:(intros a Ha; apply KEEPT; clear - Ha Hmf0 Hmfb H47 C1 Has; lia) Usp Us0 ltac:(rewrite Ura; clear - HBLO; lia)) as (ch & HCH & Hchs).
assert (Hlive : blocks_bytes S2 + k <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ (proj1 Hbl)), app_nil_l, <- (blocks_bytes_bsum B (e_ly g) (e_S g)).
  unfold LIVE_LLVMF in HLIVE. clear - Hlive0 HLIVE Hkr. lia. }
assert (Hnev : st_nev S2 < EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hn2 & _). unfold EV_LLVMF in HEV. clear - Hn2 Hnev0 HEV Hi64. lia. }
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0. pose proof (mo_free_nonneg MT MTL) as HF0.
pose proof (mo_malloc_mono MT MTL k 256 ltac:(lia)) as HMk. pose proof (mo_malloc_nonneg MT MTL k ltac:(lia)) as HMk0.
assert (MOKm : mo_ok MT S2 (mo_malloc MT k)).
{ apply (mo_ok_le MT MTL S2 (mo_malloc MT k) ((EV_LLVMF - 4 * Z.of_nat i) * (mo_malloc MT 256 + mo_free MT)) MOK).
  unfold EV_LLVMF. clear - HM0 HF0 HMk Hi64. nia. }
eapply SRr_mono.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT AMALLOC4 W2 regsT memT LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 mdT (4 * Z.of_nat i) k (mf - e_sp0 g)
    (Z_to_bv 64 (BASE + 0x4c0)) ch HJT R10).
  - unfold MALLOC_MAX. clear - Hkr. lia.
  - exact Hlive.
  - rewrite Usp. clear. lia.
  - clear - Hmf32 Hsp0al. apply Z.mod_divide in Hmf32; [|lia]. apply Z.mod_divide in Hsp0al; [|lia].
    apply Z.mod_divide; [lia|]. destruct Hmf32 as [q1 E1]. destruct Hsp0al as [q2 E2]. exists (2 * q1 - q2). lia.
  - clear - Hmfb. lia.
  - clear - HSTKm. lia.
  - exact Rgp.
  - exact Rtp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hnev.
  - exact HCH.
  - exact (d1_univ_malloc regsT 0x4c0 ch _ _ Ura ltac:(cbn; tauto) Hchs).
  - exact MOKm. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Hres & Hfr3 & Hr4 & Hbl3 & HK3 &
  MLE3 & _).
exists res. unfold D1S. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [rewrite Hfr3; exact Hfrs|].
split; [rewrite Hbl3; apply Permutation_app_comm|]. split; [constructor; [exact Hr4 | constructor]|].
split; [exact MLE3|].
split.
{ pose proof HJ3 as (HAR3 & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  assert (EFa3 : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF3; reflexivity).
  apply (d1_keep_alloc g pos mf (WR0 g pos mf) ly2 S2 W2 memT W3 mem3 (fun a => res <= a < res + req_size k)
    W2 mem2 (e_sp0 g) (mf - e_sp0 g) ltac:(rewrite Hfrs; left; reflexivity) EFa HK3 ltac:(clear; lia)).
  - intros a Ha. left. exact Ha.
  - intros a Ha. apply (d1_fz_not_block g pos ly3 S3 W3 mem3 md3 res k a HAR3).
    + rewrite Hfr3, Hfrs. left. reflexivity.
    + exact EFa3.
    + rewrite Hbl3. apply in_or_app. right. left. reflexivity.
    + exact Ha.
  - intros a Ha Hz Hn'. apply KEEPT. exact Ha. }
unfold P1. split; [exact (d1_RC_pres g pos mf i regsT regs3 HP3 HRC)|].
split; [exact Hres|].
split; [rewrite (d1_presv regsT regs3 22%bv HP3) by d1_cs; exact R22|].
split; [rewrite (d1_presv regsT regs3 27%bv HP3) by d1_cs; exact R27|].
split; [rewrite (d1_presv regsT regs3 26%bv HP3) by d1_cs; exact R26|].
rewrite (d1_presv regsT regs3 18%bv HP3) by d1_cs; exact R18.
Qed.


(* ---- Ph1's entry state ------------------------------------------------------------------------------------------ *)
Lemma d1_byte_of : forall (W : world SEGS) mem a (bs : list byte) j,
  bytes_at8 W mem a bs -> (j < length bs)%nat ->
  val_mem SEGS (rd W mem) (a + Z.of_nat j) 1 (SlotModel.inb bs (Z.of_nat j)).
Proof.
intros W mem a bs j Hb Hj. unfold bytes_at8, garr8 in Hb.
destruct (Hb j ltac:(rewrite length_map; exact Hj)) as [Hv _].
unfold SlotModel.inb, RcIdentModel.bz, RcIdentModel.nthb. rewrite Nat2Z.id.
replace (bv_unsigned (nth j bs (RcIdentModel.zb 0))) with (nth j (map (fun b : byte => bv_unsigned b) bs) 0); [exact Hv|].
rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) by (rewrite length_map; exact Hj).
apply map_nth.
Qed.

(* ---- which addresses the segment does not write (for the keep clause of D1S) ------------------------------- *)
Lemma d1_shadow_lo : forall f, 4096 <= f -> f + 1024 <= alloc_ceiling ->
  shadow_addr f + 128 < alloc_ceiling.
Proof.
intros f H0 H1. pose proof asan_consts as (C1 & _). unfold shadow_addr, SHADOW_OFF.
assert (Hq : 0 <= f / 8 /\ 8 * (f / 8) <= f) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
remember (f / 8) as q eqn:Hqe. clear Hqe. clear - H0 H1 Hq C1. lia.
Qed.
(* A byte of the machine stack (at or above mf) or of any address above the heap ceiling, outside mf+136..168. *)
Lemma d1_nwr_stack : forall g pos mf a,
  alloc_ceiling + ASTACK <= mf -> 4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
  mf <= a -> ~ (mf + 136 <= a < mf + 168) -> ~ WR1 g pos mf a.
Proof.
intros g pos mf a Hmf HSF0 HSF1 Ha Hnot.
pose proof (d1_shadow_lo (SFa g pos) HSF0 HSF1) as HSH.
assert (Has : ASTACK = 16384) by reflexivity.
unfold WR1, WR0, V_before, N_before, V_again, N_again, V_id, N_id.
intros [[H|[H|[H|[H|[H|H]]]]]|H]; try (clear - H Ha Hmf HSF0 HSF1 HSH Has; lia).
exact (Hnot H).
Qed.
(* A byte of the frame (4, pos) outside `before`, `again` and `id`. *)
Lemma d1_nwr_frame : forall g pos mf a,
  alloc_ceiling + ASTACK <= mf -> 4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
  in_app (SFa g pos) 1024 -> SFa g pos <= a < SFa g pos + 1024 ->
  ~ (SFa g pos + V_before <= a < SFa g pos + V_before + N_before) ->
  ~ (SFa g pos + V_again <= a < SFa g pos + V_again + N_again) ->
  ~ (SFa g pos + V_id <= a < SFa g pos + V_id + N_id) ->
  ~ WR1 g pos mf a.
Proof.
intros g pos mf a Hmf HSF0 HSF1 Happ Ha Hb Hg Hi.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof asan_consts as (C1 & _).
unfold WR1, WR0.
intros [[H|[H|[H|[H|[H|H]]]]]|H];
  [ clear - H Ha Hmf HSF1 Has; lia | clear - H Ha Hmf HSF1 Has; lia | exact (Hb H) | exact (Hg H)
  | | | exact (Hi H) ];
  (apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 a HSF0 ltac:(clear - HSF1 C1; lia) Happ);
   [unfold shadow_addr, SHADOW_OFF in H |- *; clear - H; lia | exact Ha]).
Qed.
(* A byte of the frame's shadow outside the five cells of `before` and the five of `again`. *)
Lemma d1_nwr_fshadow : forall g pos mf a,
  alloc_ceiling + ASTACK <= mf -> 4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
  in_app (SFa g pos) 1024 ->
  shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
  ~ (shadow_addr (SFa g pos) + 4 <= a < shadow_addr (SFa g pos) + 9) ->
  ~ (shadow_addr (SFa g pos) + 14 <= a < shadow_addr (SFa g pos) + 19) ->
  ~ WR1 g pos mf a.
Proof.
intros g pos mf a Hmf HSF0 HSF1 Happ Ha Hb Hg.
pose proof (d1_shadow_lo (SFa g pos) HSF0 HSF1) as HSH.
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
unfold WR1, WR0, V_before, N_before, V_again, N_again, V_id, N_id.
intros [[H|[H|[H|[H|[H|H]]]]]|H];
  [ clear - H Ha Hmf HSH Has; lia | clear - H Ha Hmf HSH Has; lia
  | | | exact (Hb H) | exact (Hg H) | ];
  (apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 a HSF0 ltac:(clear - HSF1 C1; lia) Happ);
   [unfold shadow_addr, SHADOW_OFF in Ha |- *; clear - Ha; lia
    | unfold V_before, N_before, V_again, N_again, V_id, N_id in H; clear - H; lia]).
Qed.
(* Carrying a value, a byte array and the two shadow facts over a memory that keeps the range. *)
Lemma d1_bytes_moved : forall (W W' : world SEGS) mem mem' a bs,
  (forall k, 0 <= k < Z.of_nat (length bs) -> aview SEGS (w_H W') mem' (a + k) = aview SEGS (w_H W) mem (a + k)) ->
  bytes_at8 W mem a bs -> bytes_at8 W' mem' a bs.
Proof.
intros W W' mem mem' a bs HK Hb j Hj. rewrite length_map in Hj.
destruct (Hb j ltac:(rewrite length_map; exact Hj)) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W') mem mem' (a + Z.of_nat j) (a + Z.of_nat j) 1); [|exact Hv].
intros k Hk. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.
Lemma d1_shblk_moved : forall (W W' : world SEGS) mem mem' a n,
  (forall k, 0 <= k < (n + 7) / 8 -> aview SEGS (w_H W') mem' (shadow_addr a + k) =
                                     aview SEGS (w_H W) mem (shadow_addr a + k)) ->
  sh_blk W mem a n -> sh_blk W' mem' a n.
Proof.
intros W W' mem mem' a n HK Hs. unfold sh_blk in *.
apply (block_shadow_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W') mem') SHADOW_OFF a n); [|exact Hs].
intros k Hk. change (shadow_of_addr SHADOW_OFF a) with (shadow_addr a). apply (HK k Hk).
Qed.
Lemma d1_shzero_moved : forall (W W' : world SEGS) mem mem' a n,
  (forall k, 0 <= k < n / 8 -> aview SEGS (w_H W') mem' (shadow_addr a + k) =
                               aview SEGS (w_H W) mem (shadow_addr a + k)) ->
  sh_zero W mem a n -> sh_zero W' mem' a n.
Proof.
intros W W' mem mem' a n HK Hs k Hk. unfold sh_zero, zero_shadow in Hs.
change (shadow_of_addr SHADOW_OFF a) with (shadow_addr a) in Hs |- *. rewrite (HK k Hk). exact (Hs k Hk).
Qed.

(* ---- the phases' statements: each is proved in its own file ------------------------------------------------- *)
(* Ph2 0x80bcc..0x80bf4: the NULL check of pl, mf+144, memcpy(pl, body, k) when k > 0. *)
Definition d1_ph2_stmt : Prop :=
  forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  D1S g pos mf i ly2 S2 W2 mem2 1 (BASE + 0x4c0) (mo_malloc MT (D1k g i)) [(pl, D1k g i)] (WR0 g pos mf) (P1 g pos mf i pl) W3 c3 ->
  SRr SEGS W3 c3 (D1S g pos mf i ly2 S2 W2 mem2 1 (BASE + 0x4e8) (mo_malloc MT (D1k g i)) [(pl, D1k g i)] (WR0 g pos mf) (P2 g pos mf i pl)).

(* Ph3 0x80bf4..0x80c1c: before's shadow and memcpy(before, id, 38). *)
Definition d1_ph3_stmt : Prop :=
  forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  D1S g pos mf i ly2 S2 W2 mem2 1 (BASE + 0x4e8) (mo_malloc MT (D1k g i)) [(pl, D1k g i)] (WR0 g pos mf) (P2 g pos mf i pl) W3 c3 ->
  SRr SEGS W3 c3 (D1S g pos mf i ly2 S2 W2 mem2 1 (BASE + 0x510) (mo_malloc MT (D1k g i)) [(pl, D1k g i)] (WR0 g pos mf) (P3 g pos mf i pl)).

(* Ph4 0x80c1c..0x80c30: reac_identity_ingest(&id, addr, pl, k). *)
Definition d1_ph4_stmt : Prop :=
  forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  D1S g pos mf i ly2 S2 W2 mem2 1 (BASE + 0x510) (mo_malloc MT (D1k g i)) [(pl, D1k g i)] (WR0 g pos mf) (P3 g pos mf i pl) W3 c3 ->
  SRr SEGS W3 c3 (D1S g pos mf i ly2 S2 W2 mem2 1 (BASE + 0x524) (mo_malloc MT (D1k g i)) [(pl, D1k g i)] (WR1 g pos mf) (P4 g pos mf i pl)).

(* Ph5 0x80c30..0x80c44: the result is >= 0, malloc(k + 1). *)
Definition d1_ph5_stmt : Prop :=
  forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  D1S g pos mf i ly2 S2 W2 mem2 1 (BASE + 0x524) (mo_malloc MT (D1k g i)) [(pl, D1k g i)] (WR1 g pos mf) (P4 g pos mf i pl) W3 c3 ->
  SRr SEGS W3 c3 (fun W4 c4 => exists gb, D1S g pos mf i ly2 S2 W2 mem2 2 (BASE + 0x538) (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1)) [(gb, D1k g i + 1); (pl, D1k g i)] (WR1 g pos mf)
    (P5 g pos mf i pl gb) W4 c4).

(* Ph6 0x80c44..0x80c64: the NULL check of gb, memcpy(gb, pl, k) when k > 0. *)
Definition d1_ph6_stmt : Prop :=
  forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W3 c3,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  D1S g pos mf i ly2 S2 W2 mem2 2 (BASE + 0x538) (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1)) [(gb, D1k g i + 1); (pl, D1k g i)] (WR1 g pos mf) (P5 g pos mf i pl gb) W3 c3 ->
  SRr SEGS W3 c3 (D1S g pos mf i ly2 S2 W2 mem2 2 (BASE + 0x558) (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1)) [(gb, D1k g i + 1); (pl, D1k g i)] (WR1 g pos mf) (P6 g pos mf i pl gb)).

(* Ph7 0x80c64..0x80cb8: mf+152/160, the checked store gb[k] := 'Z', mf+136, again's shadow, memcpy(again, before, 38). *)
Definition d1_ph7_stmt : Prop :=
  forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W3 c3,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  D1S g pos mf i ly2 S2 W2 mem2 2 (BASE + 0x558) (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1)) [(gb, D1k g i + 1); (pl, D1k g i)] (WR1 g pos mf) (P6 g pos mf i pl gb) W3 c3 ->
  SRr SEGS W3 c3 (D1S g pos mf i ly2 S2 W2 mem2 2 (BASE + 0x5ac) (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1)) [(gb, D1k g i + 1); (pl, D1k g i)] (WR1 g pos mf) (P7 g pos mf i pl gb)).

(* Ph8 0x80cb8..0x80ccc: reac_identity_ingest(&again, addr, gb, k). *)
Definition d1_ph8_stmt : Prop :=
  forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W3 c3,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  D1S g pos mf i ly2 S2 W2 mem2 2 (BASE + 0x5ac) (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1)) [(gb, D1k g i + 1); (pl, D1k g i)] (WR1 g pos mf) (P7 g pos mf i pl gb) W3 c3 ->
  SRr SEGS W3 c3 (D1S g pos mf i ly2 S2 W2 mem2 2 (BASE + 0x5c0) (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1)) [(gb, D1k g i + 1); (pl, D1k g i)] (WR1 g pos mf) (P8 g pos mf i pl gb)).

(* Ph9 0x80ccc..0x80cd8: free(gb). *)
Definition d1_ph9_stmt : Prop :=
  forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W3 c3,
  D1ctx g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  D1S g pos mf i ly2 S2 W2 mem2 2 (BASE + 0x5c0) (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1)) [(gb, D1k g i + 1); (pl, D1k g i)] (WR1 g pos mf) (P8 g pos mf i pl gb) W3 c3 ->
  SRr SEGS W3 c3 (D1S g pos mf i ly2 S2 W2 mem2 3 (BASE + 0x5cc) (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1) + mo_free MT) [(pl, D1k g i)] (WR1 g pos mf) (P9 g pos mf i pl)).

End c.
End b.
End a.
