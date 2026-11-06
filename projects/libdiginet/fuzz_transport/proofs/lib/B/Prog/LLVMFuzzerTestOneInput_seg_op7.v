(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 302 of its 413 lines of code are new or changed and 1028 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths and module names changed; 212 of its 261 lines of code are new or changed and 364 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op7: Lemma lc_op7_ok : lc_op7_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment OP7 of the image-B walk of LLVMFuzzerTestOneInput, offsets +0x7a8 .. +0x7b0 of the listing
   lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan 0x81a48 .. 0x81a50), from the cut ARM7 to the cut TAIL.

   What the code does. +0x7a8 `ld a0, 0xb8(s1)` reloads g_fail_next's auipc page from the spill slot at sp1 + 184,
   which holds transportb_hi 10 (segs.v lf_spill_scal, inside lf_spill_loop); +0x7ac `sb s6, 0x678(a0)`: s6 = 1
   (segs.v lc_s46) and transportb_hi 10 + 0x678 = TB_g_fail_next (segs.v lf_spill_globals), so the plain one-byte
   store writes 1 at the one payload byte of g_fail_next; +0x7b0 `j` to the tail +0x1670.

   One run of the token engine (lib/B/Prog/TransportGRunB.v paj_run_to_x) from ARM7 to TAIL, over two regions: the
   eight bytes of the spill slot at s1 + 184, read-only, holding the page as a literal (its value from the cut's
   lc_spills), and the one byte of g_fail_next at its absolute address, writable (the store's address folds to the
   literal TB_g_fail_next, so the region's base is None). That byte is a byte of G (TWorldB.v TMAP_B_g_fail_next), so
   the run's write right is W_journalG.v awr_ok_x_cons_g. Every other byte is kept (the run's frame), so the cut's
   core carries over by LLVMFuzzerTestOneInput_st.v lc_core_kept (the byte is an image byte, so no byte of a block or
   of the class-2 frame; it lies below alloc_ceiling and below the shadow), and the world relation moves to
   TW.set_g_fail_next (lo_B op) 1 by TWorldG.v tw_write. The model's operation equation is
   LLVMFuzzerTestOneInput_st.v lc_op7_eq at the stream fun _ => 1 (recv_addr_ok 1); the operation receives nothing,
   so k stays lo_k op. Every register but a0 is the cut's. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The symbolic state at ARM7: the eight bytes of the spill slot at s1 + 184 (atom 9), read-only, holding the page
   transportb_hi 10 as a literal; and g_fail_next's one byte at its absolute address, writable (no shadow entry: the
   store is not checked). *)
Definition OP7_PC : Z := AF_LLVMFuzzerTestOneInput + 0x7a8.
Definition OP7_STOP : Z := AF_LLVMFuzzerTestOneInput + LO_TAIL.
Definition OP7_PG : Z := transportb_hi 10.
Definition op7_fn : YP09.region :=
  YP09.mkRegion None TB_g_fail_next (TB_g_fail_next + 1) TB_g_fail_next (TB_g_fail_next + 1) [].
Definition op7_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (YP09.CVal 8 (SLit OP7_PG))].
Definition op7_ss : sstate := mkSS OP7_PC sr_atoms [op7_fn; op7_sp] None (mkFacts [] [] []).
Definition OP7_Bx : sv := SOff 26 0.
Definition OP7_B0 : Z * Z := YC4b.Bspan.

Lemma op7_inG : W_journalG.inG TG.G_HARNESS_B TB_g_fail_next.
Proof.
unfold W_journalG.inG. apply Exists_exists. exists (TB_g_fail_next, 1).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_fail_next) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The model's store g_fail_next = 1 as TWorldG.v tw_write states a one-byte store at offset 0 of the row. *)
Lemma op7_w : forall Bw, TW.set_g_fail_next Bw 1 = TW.upd Bw (TW.OFF_g_fail_next + 0) (TW.put 1 1).
Proof. intros Bw. unfold TW.set_g_fail_next. rewrite Z.add_0_r. reflexivity. Qed.

Section op7. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition op7_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma op7_ureg : forall regs (r : bv 5) (n : nat) (v : Z),
  Z.of_nat n = bv_unsigned r -> YK11.getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (op7_E regs) n) = v.
Proof.
intros regs r n v Hn Hr Hv. unfold op7_E.
rewrite (can_ew_Eimg_Ereg_nat regs [] n r Hn), Hr. unfold w64. apply unsigned_lit_small. exact Hv.
Qed.

(* The symbolic state at ARM7 holds of the machine state there. *)
Lemma op7_entry {fx : YK11.FPState} : forall (W : world segs) regs mem sp1,
  YK11.getr regs 9 = w64 sp1 ->
  alloc_ceiling <= sp1 -> sp1 + 216 <= 2 ^ 47 ->
  rdword (aview segs (w_H W) mem) (sp1 + 184) = Some OP7_PG ->
  st_ok_pi segs VAL (op7_E regs) op7_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OP7_PC)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem sp1 R9 Hlo Hhi HW.
pose proof asan_consts as (CA & _).
assert (Hsp : 0 <= sp1 < 2 ^ 64) by lia.
pose proof (op7_ureg regs 9 9%nat sp1 eq_refl R9 Hsp) as U9.
assert (TAv : TB_g_fail_next = 6155680) by reflexivity.
rewrite restrict_mkst_fx. unfold op7_ss.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold op7_fn, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (0 + o) with TB_g_fail_next by lia.
    exact (gx_rw_writable segs TG.G_HARNESS_B TB_g_fail_next G_HARNESS_B_rw op7_inG _).
  + unfold op7_sp, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs (op7_E regs) _ sp1 184 8 (SLit OP7_PG) OP7_PG);
      [reflexivity | vm_compute; split; [discriminate | reflexivity] | cbn; lia |].
    cbn [N.to_nat]. exact (val_mem_of_rdword segs (w_H W) mem (sp1 + 184) OP7_PG HW).
- unfold op7_fn, op7_sp. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9. split; [split; [left; lia | exact I] | split; exact I].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.

(* A byte of a block of the allocator is a byte of the address space. *)
Lemma op7_blk_rng : forall ly S (W : world segs) mem md p n i,
  @AR rc segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> 0 <= p + i < 2 ^ 64.
Proof.
intros ly S W mem md p n i (M & _) Hin Hi.
apply In_ablocks in Hin as (k & Hk & _ & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & _).
rewrite Hn in G8. rewrite Hu in G4. destruct G1 as [G1 _]. pose proof ASAN_CEIL_range as GC. lia.
Qed.

(* The register r at the end of the run is the one at the cut, when the run's symbolic value of r is its atom. *)
Ltac op7_kr KR H := etransitivity; [apply KR; vm_compute; reflexivity | exact H].

Lemma lc_op7_ok : lc_op7_stmt B MT XL RLO RHI.
Proof.
unfold lc_op7_stmt. intros HP cx op W' c' HB HA.
destruct HA as (ly' & S' & regs' & mem' & md' & e & Ec & Ho & HL & Htw & Hcur0 & Hcur1 & R20 & R22).
subst c'.
pose proof HL as (HC & Hfr & Hsp & Hfsh & Hopok & He & Hmet & R19).
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof asan_consts as (CA & _).
assert (TAv : TB_g_fail_next = 6155680) by reflexivity.
assert (TAimg : in_img segs TB_g_fail_next) by exact (trans_g_img TB_g_fail_next op7_inG).
(* the spill slot at sp1 + 184 holds g_fail_next's page *)
assert (HWsp : rdword (aview segs (w_H W') mem') (lc_sp1 cx + 184) = Some OP7_PG).
{ unfold lc_spills in Hsp. rewrite Forall_forall in Hsp.
  exact (Hsp (184, OP7_PG) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm, OP7_PG;
    cbn [app In]; repeat (first [left; reflexivity | right]))). }
assert (HSPhi : lc_sp1 cx + 216 <= 2 ^ 47).
{ destruct Hstk as (_ & _ & Hs0 & Hs47). unfold lc_sp0, LF_FRAME in *. lia. }
assert (HSPlo : alloc_ceiling <= lc_sp1 cx) by lia.
(* ---- +0x7a8 .. +0x7b0: ld a0, 0xb8(s1); sb s6, 0x678(a0); j to the tail ---- *)
pose proof (@op7_entry (l_fx cx) W' regs' mem' (lc_sp1 cx) R9 HSPlo HSPhi HWsp) as HS.
assert (HEI : img_env VAL A_LIM (op7_E regs')) by (unfold op7_E; apply Eimg_env).
assert (SHOK : sh_ok segs OP7_Bx (@nil shent) (op7_E regs') (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (EPC : w64 (transportb_text + lo_arm 7) = Z_to_bv 64 (BASE + OP7_PC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK OP7_B0 OP7_STOP.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_cons_g; [|apply awr_ok_x_nil]].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    replace a with TB_g_fail_next by lia. exact op7_inG.
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. exfalso. lia. }
set (md2 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md2. clear mat.
(* the run wrote g_fail_next's byte only *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> TB_g_fail_next ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha Hna.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => x = TB_g_fail_next) HFr); [| exact Ha | exact Hna].
  intros b wlo whi x Hin' Hx.
  lazymatch type of Hin' with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin' end.
  cbn [In] in Hin'.
  repeat (destruct Hin' as [Hin' | Hin']; [injection Hin' as <- <- <-; cbn [base_val] in Hx; lia |]).
  destruct Hin'. }
(* the registers: every one but a0 is the cut's *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  assert (KR : forall r : bv 5, sr_get (ss_regs ssf) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    YK11.getr (ms_regs ms) r = YK11.getr regs' r) end.
{ intros r Hs.
  assert (Hrn : Z.of_nat (Z.to_nat (bv_unsigned r)) = bv_unsigned r)
    by (apply Z2Nat.id; pose proof (bv_unsigned_in_range 5 r) as Hr; lia).
  rewrite (st_ok_pi_restrict_reg (w_H W') (op7_E regs') _ ms r HS), Hs. cbn [sv_denot].
  unfold op7_E. rewrite (can_ew_Eimg_Ereg_nat regs' [] (Z.to_nat (bv_unsigned r)) r Hrn).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (PRES : aregs_preserved regs' (ms_regs ms)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  repeat (destruct Hc as [Hc | Hc]; [subst r; apply KR; vm_compute; reflexivity |]).
  subst r. apply KR. vm_compute. reflexivity. }
(* the byte it wrote is 1: the store's symbolic value is s6's atom, and s6 = 1 at the cut *)
pose proof (st_ok_pi_restrict_reg (w_H W') (op7_E regs') _ ms 22 HS) as EQ22.
lazymatch type of EQ22 with _ = sv_denot _ ?sv =>
  let sv' := eval vm_compute in sv in change sv with sv' in EQ22 end.
assert (EV22 : YK11.getr (ms_regs ms) 22 = w64 1) by (op7_kr KR R22).
rewrite EV22 in EQ22.
assert (KV : aview segs (w_H W') (ms_mem ms) TB_g_fail_next = Some 1).
{ pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  destruct RG0 as (_ & _ & _ & RGc).
  cbn [YP09.r_base YP09.r_chunks base_val] in RGc.
  pose proof (Forall_inv RGc) as HCk. unfold YP09.chunk_ok in HCk.
  cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HCk.
  destruct (HCk 0 ltac:(lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1.
  rewrite <- EQ22 in Hb1. cbn [byte_of_word] in Hb1. injection Hb1 as <-.
  unfold aview.
  lazymatch type of Hb2 with _ = ?rhs =>
    replace (mbyte segs (mrestrict (w_H W') (ms_mem ms)) TB_g_fail_next) with rhs
      by (first [exact Hb2 | exact (eq_sym Hb2)]) end.
  vm_compute. reflexivity. }
(* the machine state at the tail *)
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ ?pc _ _) _) _ =>
  assert (EPC2 : pc = w64 (transportb_text + LO_TAIL)) by (unfold w64; f_equal; vm_compute; reflexivity);
  rewrite EPC2 end.
apply SRr_ret.
(* the bytes the cut's facts read *)
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - 0 <= a < lc_sp1 cx) ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha _. apply KM; lia. }
assert (KB : forall i, 0 <= i < l_n cx ->
  aview segs (w_H W') (ms_mem ms) (l_p cx + i) = aview segs (w_H W') mem' (l_p cx + i)).
{ intros i Hi.
  assert (Hin : In (l_p cx, l_n cx) (ablocks B ly' S')) by (apply HINg; lia).
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (_ & Hrq).
  apply KM; [exact (op7_blk_rng ly' S' W' mem' md' (l_p cx) (l_n cx) i HARg Hin ltac:(lia))|].
  intros Heq. apply (blk_img segs B LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) (l_p cx + i) HARg Hin ltac:(lia)).
  rewrite Heq. exact TAimg. }
assert (KFa : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha. unfold LF_FBYTES in *. apply KM; [lia|]. intros Heq.
  apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HARg HFin);
    [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia | rewrite Heq; exact TAimg]. }
assert (KSH : forall a, lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha. unfold lc_SH, SHADOW_OFF, LF_FBYTES in *. apply KM; [|lia].
  split; [|lia]. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). lia. }
assert (KSP : forall a, lc_sp1 cx <= a < lc_sp1 cx + 216 ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha. apply KM; lia. }
assert (TW2 : lc_tw W' (ms_mem ms) (TW.set_g_fail_next (lo_B op) 1)).
{ unfold lc_tw in Htw |- *. rewrite op7_w.
  apply (tw_write TMAP_B (aview segs (w_H W') mem') _ (lo_B op) TW.OFF_g_fail_next TB_g_fail_next 1 0 1%nat 1
    TMAP_B_ok Htw TMAP_B_g_fail_next ltac:(lia) ltac:(cbn [Z.of_nat]; lia)).
  - intros j Hj. assert (Hj0 : j = 0%nat) by lia. subst j. cbn [Z.of_nat]. rewrite !Z.add_0_r, KV.
    vm_compute. reflexivity.
  - intros x Hx Hnx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KM; [lia | intros Heq; apply Hnx; cbn [Z.of_nat]; lia]. }
unfold lc_st_tail.
exists ly', S', (ms_regs ms), (ms_mem ms), md2, e, 1, (TW.set_g_fail_next (lo_B op) 1),
  (lc_oc (l_pl cx) (lo_c op)), (lo_k op).
destruct Hfr as [F18 F26]. destruct Hcur1 as [C24 C27].
split; [reflexivity|].
split.
{ unfold lc_lcore.
  split; [exact (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' mem' md' e 0 ly' S' W' (ms_regs ms) (ms_mem ms)
    md2 e HB HC HJ eq_refl (Permutation_refl _) PRES ltac:(unfold LLVMF_STK; lia) KA KB
    ltac:(intros a Ha; apply KFa; unfold LF_FBYTES in *; lia)
    ltac:(intros a Ha Hpr; exact (apresent_grows (w_H W') mem' (ms_mem ms) a HG Hpr)))|].
  split; [split; [op7_kr KR F18 | op7_kr KR F26]|].
  split.
  { apply (lc_spills_kept cx _ (aview segs (w_H W') mem')); [| exact KSP | exact Hsp].
    intros o Hoo. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as V.
    rewrite Forall_forall in V. destruct (V o Hoo) as (_ & _ & V1 & V2). lia. }
  split; [exact (lc_fsh_kept cx (aview segs (w_H W') mem') _ false false KSH Hfsh)|].
  split; [exact Hopok|]. split; [exact He|]. split; [exact Hmet|].
  op7_kr KR R19. }
split; [unfold recv_addr_ok; lia|].
split; [exact (lc_op7_eq timg_B (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op) (eq_sym Ho))|].
split; [exact TW2|].
split; [split; [op7_kr KR C24 | op7_kr KR C27]|].
split; [op7_kr KR R20 | op7_kr KR R22].
Qed.

End op7.
