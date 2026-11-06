(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 299 of its 411 lines of code are new or changed and 1027 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module names changed; 178 of its 226 lines of code are new or changed and 363 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op7: Lemma lc_op7_ok : lc_op7_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment OP7 of the image-A walk of LLVMFuzzerTestOneInput, offsets +0x5dc .. +0x5e4 of the listing
   lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x81840 .. 0x81848), from the cut ARM7 to the cut TAIL.

   What the code does. +0x5dc `li a0, 1`; +0x5e0 `sb a0, -1076(s4)`: s4 holds g_fail_next's auipc page LF_S4 (the cut
   fixes it), so the plain one-byte store writes 1 at TA_g_fail_next, the one payload byte of g_fail_next; +0x5e4 `j`
   to the tail +0x12ec.

   One run of the token engine (lib/A/Prog/TransportGRunA.v paj_run_to_x) from ARM7 to TAIL. The store's byte is a
   byte of G (TWorldA.v TMAP_A_g_fail_next), so the run's write right is W_journalG.v awr_ok_x_cons_g. Every other byte
   is kept (the run's frame), so the cut's core carries over by LLVMFuzzerTestOneInput_st.v lc_core_kept (the byte is
   an image byte, so no byte of a block or of the class-2 frame; it lies below alloc_ceiling and below the shadow), and the
   world relation moves to TW.set_g_fail_next (lo_B op) 1 by TWorldG.v tw_write. The model's operation equation is
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The symbolic state at ARM7: g_fail_next's one byte, at s4 - 1076 (s4 holds its auipc page, LF_S4), as a writable
   region of atom 20; no shadow entry (the store is not checked). *)
Definition OP7_PC : Z := AF_LLVMFuzzerTestOneInput + 0x5dc.
Definition OP7_STOP : Z := AF_LLVMFuzzerTestOneInput + LO_TAIL.
Definition op7_rg : YP09.region := YP09.mkRegion (Some 20%nat) (-1076) (-1075) (-1076) (-1075) [].
Definition op7_ss : sstate := mkSS OP7_PC sr_atoms [op7_rg] None (mkFacts [(20%nat, mkAF LF_S4 LF_S4 0)] [] []).
Definition OP7_Bx : sv := SOff 26 0.
Definition OP7_B0 : Z * Z := YC4b.Bspan.

Lemma op7_s4 : LF_S4 - 1076 = TA_g_fail_next.
Proof. vm_compute. reflexivity. Qed.

Lemma op7_inG : W_journalG.inG TG.G_HARNESS TA_g_fail_next.
Proof.
unfold W_journalG.inG. apply Exists_exists. exists (TA_g_fail_next, 1).
split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_fail_next) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The model's store g_fail_next = 1 as TWorldG.v tw_write states a one-byte store at offset 0 of the row. *)
Lemma op7_w : forall Bw, TW.set_g_fail_next Bw 1 = TW.upd Bw (TW.OFF_g_fail_next + 0) (TW.put 1 1).
Proof. intros Bw. unfold TW.set_g_fail_next. rewrite Z.add_0_r. reflexivity. Qed.

Section op7. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition op7_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

Lemma op7_u20 : forall regs, YK11.getr regs 20 = w64 LF_S4 -> bv_unsigned (ew (op7_E regs) 20) = LF_S4.
Proof.
intros regs R20. unfold op7_E. rewrite (can_ew_Eimg_Ereg_nat regs [] 20%nat 20%bv eq_refl), R20.
unfold w64. apply unsigned_lit_small. pose proof op7_s4 as ES. unfold TA_g_fail_next in ES. lia.
Qed.

(* The symbolic state at ARM7 holds of the machine state there. *)
Lemma op7_entry {fx : YK11.FPState} : forall (W : world segs) regs mem,
  YK11.getr regs 20 = w64 LF_S4 ->
  st_ok_pi segs VAL (op7_E regs) op7_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OP7_PC)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem R20.
pose proof (op7_u20 regs R20) as U20.
rewrite restrict_mkst_fx. unfold op7_ss.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [op7_rg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U20. pose proof op7_s4 as ES.
  split; [unfold TA_g_fail_next in ES; lia|]. split; [unfold TA_g_fail_next in ES; lia|].
  split; [|constructor].
  intros o Ho. replace (LF_S4 + o) with TA_g_fail_next by lia.
  exact (gx_rw_writable segs TG.G_HARNESS TA_g_fail_next G_HARNESS_rw op7_inG _).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U20, Z.pow_0_r, Z.mod_1_r. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
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
pose proof HL as (HC & Hfr & Hsp & Hfsh & Hopok & He & Hmet & R21).
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof asan_consts as (CA & _).
pose proof (op7_u20 regs' R20) as U20.
pose proof op7_s4 as ES4.
assert (TAv : TA_g_fail_next = 0x5df120) by reflexivity.
assert (TAimg : in_img segs TA_g_fail_next) by exact (trans_g_img TA_g_fail_next op7_inG).
(* ---- +0x5dc .. +0x5e4: li a0, 1; sb a0, -1076(s4); j to the tail ---- *)
pose proof (@op7_entry (l_fx cx) W' regs' mem' R20) as HS.
assert (HEI : img_env VAL A_LIM (op7_E regs')) by (unfold op7_E; apply Eimg_env).
assert (SHOK : sh_ok segs OP7_Bx (@nil shent) (op7_E regs') (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
assert (EPC : w64 (transport_text + lo_arm 7) = Z_to_bv 64 (BASE + OP7_PC))
  by (unfold w64; f_equal; vm_compute; reflexivity).
unfold lc_cfg. rewrite EPC.
paj_run_to_tok RUNTO HS HJ SHOK OP7_B0 OP7_STOP.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U20 in Ha.
  replace a with TA_g_fail_next by lia. exact op7_inG. }
set (md2 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md2. clear mat.
(* the run wrote g_fail_next's byte only *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> TA_g_fail_next ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha Hna.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => x = TA_g_fail_next) HFr); [| exact Ha | exact Hna].
  intros b wlo whi x Hin' Hx.
  lazymatch type of Hin' with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin' end.
  cbn [In] in Hin'. destruct Hin' as [Hin' | []]. injection Hin' as <- <- <-.
  cbn [base_val] in Hx. rewrite U20 in Hx. lia. }
(* the byte it wrote is 1 *)
assert (KV : aview segs (w_H W') (ms_mem ms) TA_g_fail_next = Some 1).
{ pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  pose proof (can_field_of_region _ _ 20 LF_S4 _ (-1076) (-1075) (-1076) (-1075) (-1076) 1%N (SLit 1) 1 RG0 U20
    ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
  pose proof (HV 0%nat ltac:(lia)) as H0.
  replace (LF_S4 + -1076 + Z.of_nat 0) with TA_g_fail_next in H0 by (cbn [Z.of_nat]; lia).
  unfold aview.
  lazymatch type of H0 with _ = ?rhs =>
    replace (mbyte segs (mrestrict (w_H W') (ms_mem ms)) TA_g_fail_next) with rhs
      by (first [exact H0 | exact (eq_sym H0)]) end.
  vm_compute. reflexivity. }
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
(* the machine state at the tail *)
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ ?pc _ _) _) _ =>
  assert (EPC2 : pc = w64 (transport_text + LO_TAIL)) by (unfold w64; f_equal; vm_compute; reflexivity);
  rewrite EPC2 end.
apply SRr_ret.
(* the bytes the cut's facts read *)
assert (KA : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - 0 <= a < lc_sp1 cx) ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha _. apply KM; lia. }
assert (KB : forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
  aview segs (w_H W') (ms_mem ms) (b + i) = aview segs (w_H W') mem' (b + i)).
{ intros b m i Hbm Hi. apply KM; [exact (op7_blk_rng ly' S' W' mem' md' b m i HARg Hbm Hi)|].
  intros Heq. apply (blk_img segs B LAWS ly' S' W' mem' md' b m (b + i) HARg Hbm ltac:(lia)).
  rewrite Heq. exact TAimg. }
assert (KF : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a [Ha | Ha].
  - unfold LF_FBYTES in *. apply KM; [lia|]. intros Heq.
    apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HARg HFin);
      [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia | rewrite Heq; exact TAimg].
  - unfold lc_SH, SHADOW_OFF, LF_FBYTES in *. apply KM; [|lia].
    split; [|lia]. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). lia. }
assert (KSP : forall a, lc_sp1 cx <= a < lc_sp1 cx + 192 ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha. destruct Hstk as (_ & _ & Hs0 & Hs47). unfold lc_sp0, LF_FRAME in *. apply KM; lia. }
assert (TW2 : lc_tw W' (ms_mem ms) (TW.set_g_fail_next (lo_B op) 1)).
{ unfold lc_tw in Htw |- *. rewrite op7_w.
  apply (tw_write TMAP_A (aview segs (w_H W') mem') _ (lo_B op) TW.OFF_g_fail_next TA_g_fail_next 1 0 1%nat 1
    TMAP_A_ok Htw TMAP_A_g_fail_next ltac:(lia) ltac:(cbn [Z.of_nat]; lia)).
  - intros j Hj. assert (Hj0 : j = 0%nat) by lia. subst j. cbn [Z.of_nat]. rewrite !Z.add_0_r, KV.
    vm_compute. reflexivity.
  - intros x Hx Hnx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KM; [lia | intros Heq; apply Hnx; cbn [Z.of_nat]; lia]. }
unfold lc_st_tail.
exists ly', S', (ms_regs ms), (ms_mem ms), md2, e, 1, (TW.set_g_fail_next (lo_B op) 1), (lc_oc (l_pl cx) (lo_c op)),
  (lo_k op).
destruct Hfr as [F18 F26]. destruct Hcur1 as [C24 C23].
split; [reflexivity|].
split.
{ unfold lc_lcore.
  split; [exact (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' mem' md' e 0 ly' S' W' (ms_regs ms) (ms_mem ms)
    md2 e LAWS HB HC HJ eq_refl (Permutation_refl _) PRES ltac:(unfold LLVMF_STK; lia) KA KB KF)|].
  split; [split; [op7_kr KR F18 | op7_kr KR F26]|].
  split.
  { apply (lc_spills_kept cx _ (aview segs (w_H W') mem')); [| exact KSP | exact Hsp].
    intros o Hoo. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as V.
    rewrite Forall_forall in V. destruct (V o Hoo) as (_ & _ & V1 & V2). lia. }
  split; [exact (lc_fsh_kept cx (aview segs (w_H W') mem') _ false false
    (fun a Ha => KF a (or_intror Ha)) Hfsh)|].
  split; [exact Hopok|]. split; [exact He|]. split; [exact Hmet|].
  op7_kr KR R21. }
split; [unfold recv_addr_ok; lia|].
split; [exact (lc_op7_eq timg_A (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op) (eq_sym Ho))|].
split; [exact TW2|].
split; [split; [op7_kr KR C24 | op7_kr KR C23]|].
split; [op7_kr KR R20 | op7_kr KR R22].
Qed.

End op7.
