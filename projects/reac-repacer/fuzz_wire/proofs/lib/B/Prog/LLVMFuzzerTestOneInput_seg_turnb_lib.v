(* LLVMFuzzerTestOneInput_seg_turnb_lib: what the turn_b segment of fuzz_wire.asan-ubsan's LLVMFuzzerTestOneInput
   (+0x108 .. +0x150, lib/B/Prog/LLVMFuzzerTestOneInput_segs.v u_turn_b_stmt) needs apart from the runs of the Pa
   engine, in the form of fuzz_uci's lib/B/Prog/LLVMFuzzerTestOneInput_seg_turnb_lib.v (recipes commit 0295462466b2: a callee
   rule or contract composed into the walk, its premises at the call, its post moved to the next state):
   - tb_st_m / tb_st_c / tb_st_r: the states at the return of the malloc of c (+0x110), at the join after the copy
     into c (+0x12c) and at the return of check_copy (+0x13c);
   - the facts every call reads from the slot pre and the frame invariant u_core;
   - tb_call_malloc / tb_call_cpy / tb_call_ccpy / tb_call_crd: the malloc rule (YC5d.v amalloc04_rule), the
     __asan_memcpy rule (YCbq.v aj_intrin_at at YG0d.v aintrin_realizes OCpy), check_copy's and check_read's
     contracts (the record u_prem), each applied at its call, with its post moved to the next state;
   - tb_skip / tb_exit_of: the state after the copy when fn = 0, and u_st_exit at +0x150.
   This stretch differs from fuzz_uci's turn_b: no loop and no load or store of its own; it calls the allocator (the
   trace [malloc's pc0; WIRE_LLVMF_RA_MALLOC2]), __asan_memcpy (c, f, fn) unless fn = 0, check_copy (c, f, fn), and
   check_read (c, len, slot) unless check_copy's result len is 0. check_read records no event and charges nothing, so
   both ends of `beqz a0` at +0x13c reach the same u_st_exit. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YE00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YE01 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v YCfn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import PaJournal WirePSyms WirePList WirePAddr
  WirePPa WirePPaLib WirePImg WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require check_copy_cg check_read_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. Helpers                                                          *)
(* ------------------------------------------------------------------ *)

(* A symbolic register atom's value. *)
Lemma tb_soff_denot : forall E (a : nat) w, ew E a = w -> sv_denot E (SOff a 0) = w.
Proof. intros E a w Ha. cbn [sv_denot]. rewrite Ha, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* A callee-saved register through aregs_preserved. *)
Lemma tb_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr regs2 r = YK11.getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac tb_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let x := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with x; unfold acallee_saved; lia end.
(* A register in a literal list of registers. *)
Ltac tb_in := cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).

(* A byte array moved from base a to base b, and a prefix of one. *)
Lemma tb_garr8_moved : forall segs H H' (m m' : word -> option byte) a b l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (b + j) = aview segs H m (a + j)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') b l.
Proof.
intros segs H H' m m' a b l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (b + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk. replace (b + Z.of_nat j + k) with (b + (Z.of_nat j + k)) by lia.
replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.
Lemma tb_garr8_firstn : forall segs m b (l : list Z) k, garr8 segs m b l -> garr8 segs m b (firstn k l).
Proof.
intros segs m b l k HG j Hj. rewrite length_firstn in Hj. rewrite nth_firstn.
destruct (Nat.ltb_spec j k) as [Hlt | Hge]; [|lia]. apply HG. lia.
Qed.
Lemma tb_garr8_empty : forall segs m b (l : list Z), length l = 0%nat -> garr8 segs m b l.
Proof. intros segs m b l Hl j Hj. lia. Qed.

(* The bytes data[1 .. fn] that f holds (and c after the copy), as the list garr8 reads. *)
Definition tb_fbz (cx : ucx) : list Z := map (fun b : byte => bv_unsigned b) (u_fb cx).

(* The registers turn_b keeps from +0x108 to the call of check_copy: s0 = f, s1 = fn, s2 = slot, s5 = bcast,
   s6 = size - 1 (s3 is the block size up to +0x114, then c). *)
Definition tb_keep (cx : ucx) (regs : bvmap 5 word) (f : Z) : Prop :=
  YK11.getr regs 8 = w64 f /\ YK11.getr regs 9 = w64 (u_fn cx) /\ YK11.getr regs 18 = w64 (u_slot cx) /\
  YK11.getr regs 21 = w64 (u_bc cx) /\ YK11.getr regs 22 = w64 (u_n cx - 1).

Lemma tb_keep_pres : forall cx regs regs2 f, aregs_preserved regs regs2 -> tb_keep cx regs f -> tb_keep cx regs2 f.
Proof.
intros cx regs regs2 f HP (R8 & R9 & R18 & R21 & R22). unfold tb_keep.
repeat match goal with |- context [YK11.getr regs2 ?r] => rewrite (tb_pres regs regs2 r HP) by tb_cs end.
repeat split; assumption.
Qed.
Lemma tb_keep_kept : forall cx regs regs' f, tb_keep cx regs f ->
  (forall r : bv 5, In r [8; 9; 18; 21; 22]%bv -> YK11.getr regs' r = YK11.getr regs r) -> tb_keep cx regs' f.
Proof.
intros cx regs regs' f (R8 & R9 & R18 & R21 & R22) KA. unfold tb_keep.
repeat match goal with |- context [YK11.getr regs' ?r] => rewrite (KA r ltac:(tb_in)) end.
repeat split; assumption.
Qed.

(* The eight saved words lie in [sp0 - 0x40, sp0): a view that keeps those bytes keeps them. *)
Lemma tb_saved_kept : forall cx (r r' : reader), u_saved cx r ->
  (forall a, u_sp0 cx - 64 <= a < u_sp0 cx -> r' a = r a) -> u_saved cx r'.
Proof.
intros cx r r' Hs Hk. unfold u_saved in *. rewrite Forall_forall in *. intros o Ho.
rewrite <- (Hs o Ho). apply rdword_kept. intros k Hk8.
assert (Hf : 8 <= fst o <= 64).
{ unfold wire_saved_at in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply Hk. lia.
Qed.

(* A byte the journal may write without a file range or a fake frame of the call: a new block's byte. *)
Lemma tb_tmp_of_awr : forall STK sp0 bl0 blc lyq x,
  awr_byte STK sp0 [] bl0 blc lyq [] x -> x < sp0 - STK -> in_tmp_block bl0 blc x.
Proof.
intros STK sp0 bl0 blc lyq x [Hs | [(Hf & _) | [Ht | (cid & pos & Hin & _)]]] Hx;
  [lia | destruct (inFP_nil _ Hf) | exact Ht | destruct Hin].
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The states at +0x110, +0x12c and +0x13c                          *)
(* ------------------------------------------------------------------ *)

Section tb. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* c is a block of this call: each of its bytes lies in a block live now and not at the entry. *)
Definition tb_new (cx : ucx) (ly : alayout) (S : astate) (c : Z) : Prop :=
  forall x, c <= x < c + u_fsz cx -> in_tmp_block (ablocks B (u_ly cx) (u_S cx)) (ablocks B ly S) x.

(* +0x110, the return of the malloc of c (`beqz a0` to the abort): f and c live, a0 = c. *)
Definition tb_st_m (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (f c : Z),
    c' = u_cfg cx 0x110 regs' mem' md' /\ 0 < u_n cx /\
    u_core B cx ly' S' W' regs' mem' md' [(f, u_fsz cx); (c, u_fsz cx)] (U_EV_PRE + 1) /\
    u_meter MT XL cx S' (U_C_F MT + mo_malloc MT (u_fsz cx)) /\
    tb_keep cx regs' f /\ YK11.getr regs' 10 = w64 c /\
    garr8 segs (mrestrict (w_H W') mem') f (tb_fbz cx) /\
    tb_new cx ly' S' c /\ (c + u_fsz cx <= f \/ f + u_fsz cx <= c).

(* +0x12c, the join after the copy (the return of __asan_memcpy, or the target of `beqz s6` when fn = 0): s3 = c,
   and c holds f's fn bytes. *)
Definition tb_st_c (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (f c : Z),
    c' = u_cfg cx 0x12c regs' mem' md' /\ 0 < u_n cx /\
    u_core B cx ly' S' W' regs' mem' md' [(f, u_fsz cx); (c, u_fsz cx)] (U_EV_PRE + 1) /\
    u_meter MT XL cx S' (U_C_F MT + mo_malloc MT (u_fsz cx)) /\
    tb_keep cx regs' f /\ YK11.getr regs' 19 = w64 c /\
    garr8 segs (mrestrict (w_H W') mem') f (tb_fbz cx) /\ garr8 segs (mrestrict (w_H W') mem') c (tb_fbz cx) /\
    tb_new cx ly' S' c /\ (c + u_fsz cx <= f \/ f + u_fsz cx <= c).

(* +0x13c, the return of check_copy (`beqz a0`): a0 = len, 0 <= len <= fn, and c holds fn bytes bs. *)
Definition tb_st_r (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (f c len : Z) (bs : list byte),
    c' = u_cfg cx 0x13c regs' mem' md' /\ 0 < u_n cx /\
    u_core B cx ly' S' W' regs' mem' md' [(f, u_fsz cx); (c, u_fsz cx)] (U_EV_PRE + 1 + PCPY.CC_EV) /\
    u_meter MT XL cx S' (U_C_F MT + mo_malloc MT (u_fsz cx) + PCPY.wire_check_copy_cost MT (u_fn cx)) /\
    YK11.getr regs' 8 = w64 f /\ YK11.getr regs' 18 = w64 (u_slot cx) /\ YK11.getr regs' 19 = w64 c /\
    YK11.getr regs' 10 = w64 len /\ 0 <= len <= u_fn cx /\
    Z.of_nat (length bs) = u_fn cx /\ garr8 segs (mrestrict (w_H W') mem') c (map (fun b : byte => bv_unsigned b) bs).

(* ------------------------------------------------------------------ *)
(* 3. What every call of the segment reads                             *)
(* ------------------------------------------------------------------ *)

Lemma tb_base : forall cx, u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  0 <= u_n cx < 2 ^ 26 /\ Z.of_nat (length (u_pl cx)) = u_n cx /\
  st_nev (u_S cx) + EV_LIB <= EV_MAX /\ blocks_bytes (u_S cx) + LIVE_LIB <= LIVE_MAX /\
  arodata_okS segs B RLO RHI (aview segs (w_H (u_W cx)) (u_mem cx)).
Proof.
intros cx HP HB.
unfold u_base, tfib_lib_pre_x in HB.
destruct HB as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs & Hnev & Hbb & Haro & _).
assert (Hn26 : 0 <= u_n cx < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
exact (conj Hn26 (conj (eq_sym Hlen) (conj Hnev (conj Hbb Haro)))).
Qed.

Lemma tb_J_facts : forall cx ly' S' W mem md k,
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md k ->
  u_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= u_sp0 cx /\ u_sp0 cx <= 2 ^ 47 /\
  (forall a, u_sp0 cx - LLVMF_STK <= a < u_sp0 cx -> apresent (w_H W) mem a).
Proof.
intros cx ly' S' W mem md k HJ.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (H16 & _ & Hceil & Hlo & Hhi & H47 & _).
refine (conj H16 (conj _ (conj _ Hpres))); lia.
Qed.

(* The read-only bytes check_read's leaves read: the slot pre's arodata_okS, kept by the journal's image clause. *)
Lemma tb_rom_at : forall cx ly' S' W mem md k,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md k ->
  wire_rom_view_rd W mem.
Proof.
intros cx ly' S' W mem md k HP HB HJ a Ha.
pose proof (up_ro_unowned _ _ _ _ _ HP) as HOU. pose proof (up_rom_no_errno _ _ _ _ _ HP) as HNE.
destruct (tb_base cx HP HB) as (_ & _ & _ & _ & Haro).
destruct (wire_ro_rd_scoped B HOU HNE a Ha) as [Ho He].
destruct (wire_ro_rd_rom_clean a Ha) as [Hrom _].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img segs a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
rewrite (F3 a Himg Ho He (fp_spares_closed [] a sink_closed_nil)).
apply Haro; [left; exact Hrom | exact Ho | exact He].
Qed.

(* The meter: each block is charged at its largest size, and the whole call fits XL size. *)
Lemma tb_costs : forall cx, u_prem B MT XL RLO RHI -> 0 < u_n cx ->
  0 <= mo_malloc MT (u_fsz cx) <= mo_malloc MT WIRE_RECV_MAX /\ 0 <= mo_free MT /\
  3 * mo_malloc MT WIRE_RECV_MAX + 3 * mo_free MT <= XL (u_n cx) /\
  U_C_F MT = mo_malloc MT WIRE_RECV_MAX /\
  U_C_C MT = 3 * mo_malloc MT WIRE_RECV_MAX + mo_free MT /\
  PCPY.wire_check_copy_cost MT (u_fn cx) = mo_malloc MT (u_fsz cx) + mo_free MT.
Proof.
intros cx HP Hn. pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
destruct (u_fn_range cx Hn) as (Hfn & Hfsz).
pose proof (up_cost _ _ _ _ _ HP (u_n cx) ltac:(lia)) as Hc.
unfold wire_llvmf_cost, wire_ccpy_cost_max, PCPY.wire_check_copy_cost in Hc.
change (Z.max WIRE_RECV_MAX 1) with WIRE_RECV_MAX in Hc.
pose proof (mo_malloc_mono MT ML (u_fsz cx) WIRE_RECV_MAX ltac:(lia)).
pose proof (mo_malloc_nonneg MT ML (u_fsz cx) ltac:(lia)).
pose proof (mo_free_nonneg MT ML).
unfold U_C_F, U_C_C, wire_ccpy_cost_max, PCPY.wire_check_copy_cost.
change (Z.max WIRE_RECV_MAX 1) with WIRE_RECV_MAX.
repeat split; first [reflexivity | lia].
Qed.

Lemma tb_meter_le : forall cx S c c', u_prem B MT XL RLO RHI -> u_meter MT XL cx S c -> c <= c' ->
  u_meter MT XL cx S c'.
Proof.
intros cx S c c' HP (Hle & Hmo) Hc. pose proof (up_meter_laws _ _ _ _ _ HP) as ML. split.
- exact (mo_le_mono MT ML _ _ _ _ Hle Hc).
- apply (mo_ok_le MT ML _ _ _ Hmo). lia.
Qed.

(* A call's charge m moves the meter from c to c + m. *)
Lemma tb_meter_step : forall cx S S2 c m, u_prem B MT XL RLO RHI -> u_meter MT XL cx S c -> mo_le MT S S2 m ->
  u_meter MT XL cx S2 (c + m).
Proof.
intros cx S S2 c m HP (Hle & Hmo) Hm. pose proof (up_meter_laws _ _ _ _ _ HP) as ML. split.
- exact (mo_le_trans MT ML _ _ _ _ _ Hle Hm).
- apply (mo_ok_step MT ML S S2 m); [|exact Hm].
  replace (m + (XL (u_n cx) - (c + m))) with (XL (u_n cx) - c) by lia. exact Hmo.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The frame invariant across a run and across a call               *)
(* ------------------------------------------------------------------ *)

(* A run that wrote no memory and kept sp, gp, tp and s7 .. s11 keeps the frame invariant. *)
Lemma tb_core_same : forall cx ly' S' (W : world segs) regs regs' mem md md' bl k,
  u_core B cx ly' S' W regs mem md bl k ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md' k ->
  (forall r : bv 5, In r [2; 3; 4; 23; 24; 25; 26; 27]%bv -> YK11.getr regs' r = YK11.getr regs r) ->
  u_core B cx ly' S' W regs' mem md' bl k.
Proof.
intros cx ly' S' W regs regs' mem md md' bl k (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm)
  HJ' KA.
refine (conj HJ' (conj Hfrs (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hsv Hperm))))))))))).
- unfold spZ in *. rewrite (KA 2%bv ltac:(tb_in)). exact Hsp.
- rewrite (KA 3%bv ltac:(tb_in)). exact Hgp.
- rewrite (KA 4%bv ltac:(tb_in)). exact Htp.
- rewrite (KA 23%bv ltac:(tb_in)). exact H23.
- rewrite (KA 24%bv ltac:(tb_in)). exact H24.
- rewrite (KA 25%bv ltac:(tb_in)). exact H25.
- rewrite (KA 26%bv ltac:(tb_in)). exact H26.
- rewrite (KA 27%bv ltac:(tb_in)). exact H27.
Qed.

(* A callee's post: its journal extends the frame invariant's, it keeps the callee-saved registers and the fake
   frames, its blocks are bl2 beside the caller's, and it keeps the saved words above sp1. *)
Lemma tb_core_after : forall cx ly' S' (W W2 : world segs) regsT memT mdT ly2 S2 regs2 mem2 md2 bl bl2 k k2,
  u_core B cx ly' S' W regsT memT mdT bl k ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly2 S2 W2 mem2 md2 k2 ->
  aregs_preserved regsT regs2 -> frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B (u_ly cx) (u_S cx) ++ bl2) ->
  (forall a, u_sp1 cx <= a < u_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a) ->
  u_core B cx ly2 S2 W2 regs2 mem2 md2 bl2 k2.
Proof.
intros cx ly' S' W W2 regsT memT mdT ly2 S2 regs2 mem2 md2 bl bl2 k k2
  (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm) HJ2 HPr Hfr2 Hperm2 HK.
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regsT r)
  by (intros r Hr; exact (tb_pres regsT regs2 r HPr Hr)).
refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ Hperm2))))))))))).
- rewrite Hfr2. exact Hfrs.
- unfold spZ in *. rewrite (P 2%bv ltac:(tb_cs)). exact Hsp.
- rewrite (P 3%bv ltac:(tb_cs)). exact Hgp.
- rewrite (P 4%bv ltac:(tb_cs)). exact Htp.
- rewrite (P 23%bv ltac:(tb_cs)). exact H23.
- rewrite (P 24%bv ltac:(tb_cs)). exact H24.
- rewrite (P 25%bv ltac:(tb_cs)). exact H25.
- rewrite (P 26%bv ltac:(tb_cs)). exact H26.
- rewrite (P 27%bv ltac:(tb_cs)). exact H27.
- apply (tb_saved_kept cx _ _ Hsv). intros a Ha. apply HK. unfold u_sp1, U_FRAME. lia.
Qed.

(* The blocks f and c of the frame invariant, with their bounds. *)
Lemma tb_blocks : forall cx ly' S' (W : world segs) regs mem md f c k,
  u_prem B MT XL RLO RHI -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx); (c, u_fsz cx)] k ->
  In (f, u_fsz cx) (ablocks B ly' S') /\ In (c, u_fsz cx) (ablocks B ly' S') /\
  req_size (u_fsz cx) = u_fsz cx /\ 1 <= u_fsz cx <= WIRE_RECV_MAX /\ 0 <= u_fn cx <= u_fsz cx /\
  4096 <= f /\ f + u_fsz cx <= alloc_ceiling /\ 4096 <= c /\ c + u_fsz cx <= alloc_ceiling.
Proof.
intros cx ly' S' W regs mem md f c k HP Hn HC.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm).
pose proof (proj1 HJ) as HAR.
destruct (u_fn_range cx Hn) as (Hfn & Hfsz).
assert (Ereq : req_size (u_fsz cx) = u_fsz cx) by (unfold req_size; destruct (Z.eqb_spec (u_fsz cx) 0); lia).
assert (Hfin : In (f, u_fsz cx) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hcin : In (c, u_fsz cx) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ f (u_fsz cx) HAR Hfin) as (_ & Hf4 & Hfc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c (u_fsz cx) HAR Hcin) as (_ & Hc4 & Hcc & _).
rewrite Ereq in Hfc, Hcc.
assert (u_fn cx <= u_fsz cx) by (unfold u_fsz; lia).
repeat split; first [exact Hfin | exact Hcin | exact Ereq | lia].
Qed.

(* The live bytes of the frame invariant's blocks: the caller's and two blocks of at most WIRE_RECV_MAX bytes. *)
Lemma tb_live : forall cx ly' S' bl,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  Permutation (ablocks B ly' S') (ablocks B (u_ly cx) (u_S cx) ++ bl) ->
  blocks_bytes S' = blocks_bytes (u_S cx) + bsum bl.
Proof.
intros cx ly' S' bl HP HB Hperm.
rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ Hperm), bsum_app, <- (blocks_bytes_bsum B (u_ly cx) (u_S cx)).
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The four calls                                                   *)
(* ------------------------------------------------------------------ *)

(* The malloc of c at +0x10c (a0 = s3 = fsz) by the malloc rule of u_prem; its return +0x110 is tb_st_m. s0 = f is
   below alloc_ceiling, so the chain is empty and the trace is [malloc's pc0; WIRE_LLVMF_RA_MALLOC2] (u_prem's
   wire_llvmf_ufix); f is a live block, so the depot holds a trace (WireCg.v wire_depot_of_block). *)
Lemma tb_call_malloc : forall cx (W : world segs) regsT memT mdT ly' S' f,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regsT memT mdT [(f, u_fsz cx)] U_EV_PRE -> u_meter MT XL cx S' (U_C_F MT) ->
  tb_keep cx regsT f -> YK11.getr regsT 10 = w64 (u_fsz cx) ->
  YK11.getr regsT 1 = w64 (WIRE_A_LLVMF + 0x110) ->
  garr8 segs (mrestrict (w_H W) memT) f (tb_fbz cx) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS___interceptor_trampoline_malloc) regsT memT mdT) (tb_st_m cx).
Proof.
intros cx W regsT memT mdT ly' S' f HP HB Hn HC HM HK R10 R1 HG.
pose proof (up_laws _ _ _ _ _ HP) as LAWS. pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm).
destruct (tb_base cx HP HB) as (Hn26 & Hlen & Hnev & Hbb & _).
destruct (tb_J_facts cx ly' S' W memT mdT _ HJ) as (H16 & Hceil & H47 & Hpres).
pose proof (@alloc_ceiling_val rc) as Hce.
destruct (u_fn_range cx Hn) as (Hfn & Hfsz).
assert (Hfnle : u_fn cx <= u_fsz cx) by (unfold u_fsz; lia).
unfold LLVMF_STK in Hceil.
destruct (tb_costs cx HP Hn) as (Hmf & Hfr & Hxl & EUF & EUC & ECC).
pose proof (proj1 HJ) as HAR.
assert (Ereq : req_size (u_fsz cx) = u_fsz cx) by (unfold req_size; destruct (Z.eqb_spec (u_fsz cx) 0); lia).
assert (Hfin : In (f, u_fsz cx) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ f (u_fsz cx) HAR Hfin) as (_ & Hf4096 & Hfceil & _).
rewrite Ereq in Hfceil.
pose proof HK as (R8 & R9 & R18 & R21 & R22).
assert (Hraz : raZ regsT = WIRE_A_LLVMF + 0x110)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; vm_compute; split; congruence).
assert (Hsp1 : spZ regsT = u_sp0 cx + - U_FRAME) by (rewrite Hsp; unfold u_sp1; lia).
assert (EPRE : U_EV_PRE = 1) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev' & _).
assert (Ebs : bsum [(f, u_fsz cx)] = u_fsz cx) by (unfold bsum; cbn; lia).
rewrite <- (up_wrap_malloc _ _ _ _ _ HP).
unfold cfg_at.
eapply SRr_bind.
{ eapply (up_malloc _ _ _ _ _ HP (u_fx cx) W regsT memT LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx)
    (u_mem cx) (u_md cx) [] ly' S' mdT U_EV_PRE (u_fsz cx) (- U_FRAME) (w64 (WIRE_A_LLVMF + 0x110)) [] HJ R10).
  - unfold MALLOC_MAX, WIRE_RECV_MAX in *. lia.
  - rewrite (tb_live cx ly' S' _ HP HB Hperm), Ebs. unfold LIVE_LIB, LIVE_MAX, WIRE_RECV_MAX in *. lia.
  - exact Hsp1.
  - reflexivity.
  - unfold U_FRAME. lia.
  - unfold ASTACK, LLVMF_STK, U_FRAME. lia.
  - exact Hgp.
  - exact Htp.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - rewrite EPRE in Hnev'. unfold EV_LIB, EV_MAX in *. lia.
  - apply (achain_chain_pre ly' (aview segs (w_H W) memT) (spZ regsT) f [] regsT).
    + apply achain_low. lia.
    + unfold LLVMF_STK, U_FRAME in *. lia.
    + unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. lia.
    + rewrite Hraz. vm_compute. discriminate.
  - rewrite call_trace_of_spine. cbn [spine map]. rewrite Hraz.
    pose proof (up_ufix _ _ _ _ _ HP) as (_ & U2 & _). exact U2.
  - apply (mo_ok_le MT ML S' _ _ (proj2 HM)). rewrite EUF. lia.
  - exact (wire_depot_of_block B ly' S' W memT mdT f (u_fsz cx) HAR Hfin). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & c & -> & HJ2 & HPr & R10' & Hfr2 & Hc4096 & Eab & HKp & Hmle).
apply SRr_ret.
pose proof (proj1 HJ2) as HAR2.
assert (Hcin : In (c, u_fsz cx) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c (u_fsz cx) HAR2 Hcin) as (_ & _ & Hcceil & _).
rewrite Ereq in Hcceil.
(* f and c are disjoint *)
assert (HDJ : c + u_fsz cx <= f \/ f + u_fsz cx <= c).
{ destruct (in_split _ _ Hfin) as (l1 & l2 & El).
  pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (f, u_fsz cx) (c, u_fsz cx) l1 l2 [] HAR2) as Hd.
  rewrite Eab, El, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Ereq in Hd. lia. }
destruct HKp as (K1 & K2 & _).
exists ly2, S2, regs2, mem2, md2, f, c.
refine (conj eq_refl (conj Hn (conj _ (conj _ (conj _ (conj R10' (conj _ (conj _ HDJ)))))))).
- apply (tb_core_after cx ly' S' W W2 regsT memT mdT ly2 S2 regs2 mem2 md2 _ _ U_EV_PRE (U_EV_PRE + 1) HC HJ2 HPr Hfr2).
  + rewrite Eab.
    replace (ablocks B (u_ly cx) (u_S cx) ++ [(f, u_fsz cx); (c, u_fsz cx)])
      with ((ablocks B (u_ly cx) (u_S cx) ++ [(f, u_fsz cx)]) ++ [(c, u_fsz cx)])
      by (rewrite <- app_assoc; reflexivity).
    apply Permutation_app_tail. exact Hperm.
  + intros a Ha. apply K1; unfold u_sp1, U_FRAME in *; lia.
- exact (tb_meter_step cx S' S2 _ _ HP HM Hmle).
- exact (tb_keep_pres cx regsT regs2 f HPr HK).
- apply (garr8_kept segs (w_H W) (w_H W2) memT mem2 f (tb_fbz cx)); [|exact HG].
  intros j Hj. unfold tb_fbz in Hj. rewrite length_map, (u_fb_length cx Hn (eq_sym Hlen)) in Hj.
  assert (Hj' : 0 <= j < req_size (u_fsz cx)) by (rewrite Ereq; unfold u_fsz; lia).
  apply (K2 f (u_fsz cx) j Hfin Hj'). cbv beta. rewrite Ereq. lia.
- intros x Hx.
  pose proof (awr_new_block segs B LAWS LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
    ly' S' W memT mdT U_EV_PRE ly2 S2 W2 mem2 md2 c (u_fsz cx) (ablocks B ly2 S2) (x - c) ly2 HJ HAR2 Eab
    ltac:(lia) Hcin ltac:(rewrite Ereq; lia)) as Hw.
  replace (c + (x - c)) with x in Hw by lia.
  apply (tb_tmp_of_awr _ _ _ _ _ _ Hw). unfold LLVMF_STK. lia.
Qed.

(* __asan_memcpy (c, f, fn) at +0x128 (fn > 0) by the rule of u_prem through YCbq.v aj_intrin_at: c is a block of this
   call, f a block of the frame, disjoint, both below the stack; its return +0x12c is tb_st_c. *)
Lemma tb_call_cpy : forall cx (W : world segs) regsT memT mdT ly' S' f c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx -> 0 < u_fn cx ->
  u_core B cx ly' S' W regsT memT mdT [(f, u_fsz cx); (c, u_fsz cx)] (U_EV_PRE + 1) ->
  u_meter MT XL cx S' (U_C_F MT + mo_malloc MT (u_fsz cx)) ->
  tb_keep cx regsT f -> YK11.getr regsT 19 = w64 c ->
  YK11.getr regsT 10 = w64 c -> YK11.getr regsT 11 = w64 f -> YK11.getr regsT 12 = w64 (u_fn cx) ->
  YK11.getr regsT 1 = w64 (WIRE_A_LLVMF + 0x12c) ->
  garr8 segs (mrestrict (w_H W) memT) f (tb_fbz cx) ->
  tb_new cx ly' S' c -> (c + u_fsz cx <= f \/ f + u_fsz cx <= c) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS___asan_memcpy) regsT memT mdT) (tb_st_c cx).
Proof.
intros cx W regsT memT mdT ly' S' f c HP HB Hn Hfn0 HC HM HK R19 R10 R11 R12 R1 HG HNEW HDJ.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm).
destruct (tb_base cx HP HB) as (Hn26 & Hlen & _).
destruct (tb_J_facts cx ly' S' W memT mdT _ HJ) as (H16 & Hceil & H47 & Hpres).
pose proof (@alloc_ceiling_val rc) as Hce.
unfold LLVMF_STK in Hceil.
destruct (tb_blocks cx ly' S' W regsT memT mdT f c _ HP Hn HC)
  as (Hfin & Hcin & Ereq & Hfsz & Hfnr & Hf4 & Hfc & Hc4 & Hcc).
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ f (u_fsz cx) HAR Hfin) as (_ & _ & _ & _ & Hfpres & _).
assert (Hsp1 : spZ regsT = u_sp0 cx + - U_FRAME) by (rewrite Hsp; unfold u_sp1; lia).
unfold cfg_at.
eapply SRr_bind.
{ eapply (aj_intrin_at segs B LAWS wire_segs_low OCpy (wire_sigma WS___asan_memcpy) (up_memcpy _ _ _ _ _ HP (u_fx cx))
    W regsT memT LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' mdT
    (U_EV_PRE + 1) c f (u_fn cx) (- U_FRAME) (w64 (WIRE_A_LLVMF + 0x12c)) HJ R10 R11 R12).
  - unfold WIRE_RECV_MAX in *. lia.
  - lia.
  - pose proof alloc_ceiling_lt. lia.
  - exact Hsp1.
  - reflexivity.
  - unfold U_FRAME. lia.
  - unfold ESTACK, LLVMF_STK, U_FRAME. lia.
  - exact Hgp.
  - exact Htp.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split.
    + right. right. left. apply HNEW. lia.
    + unfold LLVMF_STK, U_FRAME, ESTACK in *. lia.
  - apply (amem_range_of_block segs B LAWS ly' S' W memT mdT c (u_fsz cx) c (u_fn cx) HAR Hcin); rewrite ?Ereq; lia.
  - apply (range_addressable_of_block segs B LAWS ly' S' W memT mdT c (u_fsz cx) c (u_fn cx) HAR Hcin);
      rewrite ?Ereq; lia.
  - intros _. apply (shadow_hull_vis_of_block segs B LAWS ly' S' W memT mdT c (u_fsz cx) c (u_fn cx) HAR Hcin);
      rewrite ?Ereq; lia.
  - cbv beta iota. split; [lia|]. split; [pose proof alloc_ceiling_lt; lia|]. split.
    { intros a Ha. split.
      - apply (aview_some_of_apresent segs). apply (proj1 (Hfpres a ltac:(rewrite Ereq; lia))).
      - rewrite Hsp1. unfold ESTACK, LLVMF_STK, U_FRAME in *. lia. }
    split; [lia|]. split.
    { apply (amem_range_of_block segs B LAWS ly' S' W memT mdT f (u_fsz cx) f (u_fn cx) HAR Hfin); rewrite ?Ereq; lia. }
    split.
    { apply (range_addressable_of_block segs B LAWS ly' S' W memT mdT f (u_fsz cx) f (u_fn cx) HAR Hfin);
        rewrite ?Ereq; lia. }
    intros _. apply (shadow_hull_vis_of_block segs B LAWS ly' S' W memT mdT f (u_fsz cx) f (u_fn cx) HAR Hfin);
      rewrite ?Ereq; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPr & R10' & HCPY & HKEEP & HAPR).
apply SRr_ret.
assert (HFL : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + u_fn cx) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)
  by (intros a Ha H1 H2; apply HKEEP; [exact Ha | exact H1 | rewrite <- Hsp1; exact H2]).
exists ly', S', regs2, mem2, md2, f, c.
refine (conj eq_refl (conj Hn (conj _ (conj HM (conj _ (conj _ (conj _ (conj _ (conj HNEW HDJ))))))))).
- apply (tb_core_after cx ly' S' W W regsT memT mdT ly' S' regs2 mem2 md2 _ _ (U_EV_PRE + 1) (U_EV_PRE + 1)
    HC HJ2 HPr eq_refl Hperm).
  intros a Ha. unfold u_sp1, U_FRAME in Ha. pose proof alloc_ceiling_lt.
  apply HFL; [lia | lia | rewrite Hsp; unfold u_sp1, U_FRAME, ESTACK; lia].
- exact (tb_keep_pres cx regsT regs2 f HPr HK).
- rewrite (tb_pres regsT regs2 19%bv HPr ltac:(tb_cs)). exact R19.
- apply (garr8_kept segs (w_H W) (w_H W) memT mem2 f (tb_fbz cx)); [|exact HG].
  intros j Hj. unfold tb_fbz in Hj. rewrite length_map, (u_fb_length cx Hn (eq_sym Hlen)) in Hj.
  pose proof alloc_ceiling_lt.
  apply HFL; [lia | lia | rewrite Hsp; unfold u_sp1, U_FRAME, ESTACK; lia].
- apply (tb_garr8_moved segs (w_H W) (w_H W) memT mem2 f c (tb_fbz cx)); [|exact HG].
  intros j Hj. unfold tb_fbz in Hj. rewrite length_map, (u_fb_length cx Hn (eq_sym Hlen)) in Hj.
  exact (HCPY j Hj).
Qed.

(* check_copy (c, f, fn) at +0x138 by u_prem's contract; its return +0x13c is tb_st_r. c's bytes are a block of this
   call (in_tmp_block), as the contract asks of the bytes it writes. *)
Lemma tb_call_ccpy : forall cx (W : world segs) regsT memT mdT ly' S' f c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regsT memT mdT [(f, u_fsz cx); (c, u_fsz cx)] (U_EV_PRE + 1) ->
  u_meter MT XL cx S' (U_C_F MT + mo_malloc MT (u_fsz cx)) ->
  YK11.getr regsT 8 = w64 f -> YK11.getr regsT 18 = w64 (u_slot cx) -> YK11.getr regsT 19 = w64 c ->
  YK11.getr regsT 10 = w64 c -> YK11.getr regsT 11 = w64 f -> YK11.getr regsT 12 = w64 (u_fn cx) ->
  YK11.getr regsT 1 = w64 (WIRE_A_LLVMF + 0x13c) ->
  garr8 segs (mrestrict (w_H W) memT) f (tb_fbz cx) -> garr8 segs (mrestrict (w_H W) memT) c (tb_fbz cx) ->
  tb_new cx ly' S' c -> (c + u_fsz cx <= f \/ f + u_fsz cx <= c) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS_check_copy) regsT memT mdT) (tb_st_r cx).
Proof.
intros cx W regsT memT mdT ly' S' f c HP HB Hn HC HM R8 R18 R19 R10 R11 R12 R1 HGf HGc HNEW HDJ.
pose proof (up_laws _ _ _ _ _ HP) as LAWS. pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm).
destruct (tb_base cx HP HB) as (Hn26 & Hlen & Hnev & Hbb & _).
destruct (tb_J_facts cx ly' S' W memT mdT _ HJ) as (H16 & Hceil & H47 & Hpres).
pose proof (@alloc_ceiling_val rc) as Hce.
destruct (tb_blocks cx ly' S' W regsT memT mdT f c _ HP Hn HC)
  as (Hfin & Hcin & Ereq & Hfsz & Hfnr & Hf4 & Hfc & Hc4 & Hcc).
destruct (tb_costs cx HP Hn) as (Hmf & Hfr & Hxl & EUF & EUC & ECC).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev' & _).
assert (EPRE : U_EV_PRE = 1) by reflexivity.
assert (ECCEV : PCPY.CC_EV = 2) by reflexivity.
assert (Hraz : raZ regsT = WIRE_A_LLVMF + 0x13c)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; vm_compute; split; congruence).
assert (Ebs : bsum [(f, u_fsz cx); (c, u_fsz cx)] = 2 * u_fsz cx) by (unfold bsum; cbn; lia).
eapply SRr_bind.
{ refine (up_ccpy _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
    ly' S' W memT mdT (U_EV_PRE + 1) regsT c f (u_fn cx)
    (XL (u_n cx) - (U_C_F MT + mo_malloc MT (u_fsz cx))) (u_fb cx)
    HJ _ _ Hgp Htp R10 R11 R12 _ _ _ _ (u_fb_length cx Hn (eq_sym Hlen)) _ _ _ _ HGc HGf _ _ _ (proj2 HM) _).
  - rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
  - rewrite Hraz. vm_compute. discriminate.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME, PCPY.CC_STK, PCPY.CC_FRAME, ASTACK, LLVMF_STK. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - unfold PCPY.CC_RECV_MAX, WIRE_RECV_MAX in *. lia.
  - intros _. exists c, (u_fsz cx). split; [exact Hcin | lia].
  - intros _. exists f, (u_fsz cx). split; [exact Hfin | lia].
  - intros _. lia.
  - intros x Hx. right. apply HNEW. lia.
  - exact (wire_depot_of_block B ly' S' W memT mdT f (u_fsz cx) HAR Hfin).
  - rewrite EPRE, ECCEV. unfold EV_LIB, EV_MAX in *. lia.
  - rewrite (tb_live cx ly' S' _ HP HB Hperm), Ebs. unfold PCPY.CC_LIVE, PCPY.CC_RECV_MAX, LIVE_LIB, LIVE_MAX,
      WIRE_RECV_MAX in *. lia.
  - rewrite ECC, EUF. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & len & bs' & -> & HJ2 & HPr & Hfr2 & Hperm2 & HKp & Hmle
  & R10' & Hlen' & Hbs & HGc').
apply SRr_ret.
destruct HKp as (K1 & _).
exists ly2, S2, regs2, mem2, md2, f, c, len, bs'.
refine (conj _ (conj Hn (conj _ (conj _ (conj _ (conj _ (conj _ (conj R10' (conj Hlen' (conj Hbs HGc')))))))))).
- unfold u_cfg. rewrite R1. reflexivity.
- apply (tb_core_after cx ly' S' W W2 regsT memT mdT ly2 S2 regs2 mem2 md2 _ _ (U_EV_PRE + 1)
    (U_EV_PRE + 1 + PCPY.CC_EV) HC HJ2 HPr Hfr2 (Permutation_trans Hperm2 Hperm)).
  intros a Ha. apply K1; [pose proof alloc_ceiling_lt; unfold u_sp1, U_FRAME, LLVMF_STK in *; lia|].
  rewrite Hsp. unfold u_sp1 in *. lia.
- exact (tb_meter_step cx S' S2 _ _ HP HM Hmle).
- rewrite (tb_pres regsT regs2 8%bv HPr ltac:(tb_cs)). exact R8.
- rewrite (tb_pres regsT regs2 18%bv HPr ltac:(tb_cs)). exact R18.
- rewrite (tb_pres regsT regs2 19%bv HPr ltac:(tb_cs)). exact R19.
Qed.

(* u_st_exit at +0x150 from a state whose size, journal, meter and blocks are the exit's. *)
Lemma tb_exit_of : forall cx (W : world segs) regs mem md ly' S' f c k m,
  u_prem B MT XL RLO RHI -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx); (c, u_fsz cx)] k -> k = U_EV_EXIT ->
  u_meter MT XL cx S' m -> m <= U_C_C MT ->
  YK11.getr regs 8 = w64 f -> YK11.getr regs 19 = w64 c ->
  u_st_exit B MT XL cx W (u_cfg cx U_EXIT regs mem md).
Proof.
intros cx W regs mem md ly' S' f c k m HP Hn HC Hk HM Hm R8 R19. subst k.
exists ly', S', regs, mem, md, f, c.
exact (conj eq_refl (conj Hn (conj HC (conj (tb_meter_le cx S' m _ HP HM Hm) (conj R8 R19))))).
Qed.

(* The exit's meter: two mallocs of at most WIRE_RECV_MAX bytes and one call of check_copy. *)
Lemma tb_exit_cost : forall cx, u_prem B MT XL RLO RHI -> 0 < u_n cx ->
  U_C_F MT + mo_malloc MT (u_fsz cx) + PCPY.wire_check_copy_cost MT (u_fn cx) <= U_C_C MT.
Proof.
intros cx HP Hn. destruct (tb_costs cx HP Hn) as (Hmf & Hfr & Hxl & EUF & EUC & ECC).
rewrite EUF, EUC, ECC. lia.
Qed.

(* check_read (c, len, slot) at +0x14c by u_prem's contract; its return +0x150 is u_st_exit. Its bytes are the first
   len of the fn bytes check_copy left in c; class 1 has a free fake frame (the frame invariant has none); the
   read-only bytes are the image's (tb_rom_at). *)
Lemma tb_call_crd : forall cx (W : world segs) regsT memT mdT ly' S' f c len bs,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regsT memT mdT [(f, u_fsz cx); (c, u_fsz cx)] (U_EV_PRE + 1 + PCPY.CC_EV) ->
  u_meter MT XL cx S' (U_C_F MT + mo_malloc MT (u_fsz cx) + PCPY.wire_check_copy_cost MT (u_fn cx)) ->
  YK11.getr regsT 8 = w64 f -> YK11.getr regsT 19 = w64 c ->
  YK11.getr regsT 10 = w64 c -> YK11.getr regsT 11 = w64 len -> YK11.getr regsT 12 = w64 (u_slot cx) ->
  YK11.getr regsT 1 = w64 (WIRE_A_LLVMF + 0x150) ->
  0 <= len <= u_fn cx -> Z.of_nat (length bs) = u_fn cx ->
  garr8 segs (mrestrict (w_H W) memT) c (map (fun b : byte => bv_unsigned b) bs) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS_check_read) regsT memT mdT) (u_st_exit B MT XL cx).
Proof.
intros cx W regsT memT mdT ly' S' f c len bs HP HB Hn HC HM R8 R19 R10 R11 R12 R1 Hl Hbs HGc.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm).
destruct (tb_base cx HP HB) as (Hn26 & Hlen & Hnev & Hbb & _).
destruct (tb_J_facts cx ly' S' W memT mdT _ HJ) as (H16 & Hceil & H47 & Hpres).
pose proof (@alloc_ceiling_val rc) as Hce.
destruct (tb_blocks cx ly' S' W regsT memT mdT f c _ HP Hn HC)
  as (Hfin & Hcin & Ereq & Hfsz & Hfnr & Hf4 & Hfc & Hc4 & Hcc).
assert (EPRE : U_EV_PRE = 1) by reflexivity.
assert (ECCEV : PCPY.CC_EV = 2) by reflexivity.
assert (ECRD : PRD.CRD_EV = 0) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev' & _).
assert (Hraz : raZ regsT = WIRE_A_LLVMF + 0x150)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; vm_compute; split; congruence).
eapply SRr_bind.
{ refine (up_crd _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
    ly' S' W memT mdT (U_EV_PRE + 1 + PCPY.CC_EV) regsT c len (u_slot cx) (firstn (Z.to_nat len) bs)
    HJ _ _ Hgp Htp R10 R11 R12 _ _ _ _ _ (u_slot_int cx) _ _ _ (tb_rom_at cx ly' S' W memT mdT _ HP HB HJ) _).
  - rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
  - rewrite Hraz. vm_compute. discriminate.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME, PRD.CRD_STK, PRD.CRD_FRAME, PRD.CRD_ALIGN, ESTACK, LLVMF_STK. lia.
  - rewrite Hsp. unfold u_sp1, U_FRAME. lia.
  - unfold PRD.W_RECV_MAX, WIRE_RECV_MAX in *. lia.
  - rewrite length_firstn. lia.
  - intros _. exists c, (u_fsz cx). split; [exact Hcin | lia].
  - rewrite <- firstn_map. apply tb_garr8_firstn. exact HGc.
  - rewrite Hfrs. vm_compute. reflexivity.
  - rewrite EPRE, ECCEV, ECRD. unfold EV_LIB, EV_MAX in *. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hfr2 & Hperm2 & HKp & Hmle).
apply SRr_ret.
destruct HKp as (K1 & _).
rewrite R1. change (u_st_exit B MT XL cx W2 (u_cfg cx U_EXIT regs2 mem2 md2)).
apply (tb_exit_of cx W2 regs2 mem2 md2 ly2 S2 f c (U_EV_PRE + 1 + PCPY.CC_EV + PRD.CRD_EV)
  (U_C_F MT + mo_malloc MT (u_fsz cx) + PCPY.wire_check_copy_cost MT (u_fn cx) + 0) HP Hn).
- apply (tb_core_after cx ly' S' W W2 regsT memT mdT ly2 S2 regs2 mem2 md2 _ _ (U_EV_PRE + 1 + PCPY.CC_EV)
    (U_EV_PRE + 1 + PCPY.CC_EV + PRD.CRD_EV) HC HJ2 HPr Hfr2 (Permutation_trans Hperm2 Hperm)).
  intros a Ha. apply K1; [pose proof alloc_ceiling_lt; unfold u_sp1, U_FRAME, LLVMF_STK in *; lia|].
  rewrite Hsp. unfold u_sp1 in *. lia.
- reflexivity.
- exact (tb_meter_step cx S' S2 _ _ HP HM Hmle).
- pose proof (tb_exit_cost cx HP Hn). lia.
- rewrite (tb_pres regsT regs2 8%bv HPr ltac:(tb_cs)). exact R8.
- rewrite (tb_pres regsT regs2 19%bv HPr ltac:(tb_cs)). exact R19.
Qed.

(* The join at +0x12c reached by `beqz s6` (size = 1, so fn = 0): c holds no byte to compare. *)
Lemma tb_skip : forall cx (W : world segs) regs mem md ly' S' f c,
  0 < u_n cx -> u_fn cx = 0 ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx); (c, u_fsz cx)] (U_EV_PRE + 1) ->
  u_meter MT XL cx S' (U_C_F MT + mo_malloc MT (u_fsz cx)) ->
  tb_keep cx regs f -> YK11.getr regs 19 = w64 c ->
  garr8 segs (mrestrict (w_H W) mem) f (tb_fbz cx) ->
  tb_new cx ly' S' c -> (c + u_fsz cx <= f \/ f + u_fsz cx <= c) ->
  tb_st_c cx W (u_cfg cx 0x12c regs mem md).
Proof.
intros cx W regs mem md ly' S' f c Hn Hfn0 HC HM HK R19 HG HNEW HDJ.
exists ly', S', regs, mem, md, f, c.
refine (conj eq_refl (conj Hn (conj HC (conj HM (conj HK (conj R19 (conj HG (conj _ (conj HNEW HDJ))))))))).
apply tb_garr8_empty. unfold tb_fbz, u_fb. rewrite length_map, length_firstn, Hfn0. reflexivity.
Qed.
End tb.
