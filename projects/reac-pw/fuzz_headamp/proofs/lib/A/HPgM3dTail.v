(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the engine run from a fresh entry state and
   its re-seat at a fixed pc) for the value dispatch and the Int arm of reac-pw/fuzz_role's image-A segment M02
   (0x82318 .. 0x823e0). *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the call in the middle of a walk: the run
   to the jal, the callee's contract through SRr_bind, a fresh entry state at the return pc) for the common value
   tail of reac-pw/fuzz_role's image-A segment M02 (0x823e0 .. 0x823f8: the role's range test, check_role, the jump
   to T). *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from lib/A/RPgCheck.v at fb6520a9cda (its entry state ss_ck, regs_ok_override, the save-slot region and awr_stk / kwr_stk, ck_kept_run, the ret leaf) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_answer 0x82c30 and check_code 0x82c80 against lib/A/RPgCSpec.v's rl_check_answer_specX / rl_check_code_specX on lib/A/Img0.v rsegs. Each function is cut at its calls of the strcmp wrapper (0x41ad0): the run to the call, the call through lib/A/RPgStrcmp.v's aj_strcmp_at (the wrapper's contract astrcmp_realizes is the Section hypothesis ASTRCMP), and a fresh entry state after the call whose save slot holds the caller's ra (and s0) from the extra env slots 33 / 34; the callee-saved registers are threaded across the cuts with cs_eq. The snez-of-xor value lemma is lib/A/RPgCfgChanges.v's snez_xor_Z, restated. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyI.v at 7e8cf15c304 (the engine run from
   a fresh entry state and the rebuild of a cut at a run's last state), with the register tactic m2k_rsv of
   RPgM02KeyV.v and the lemma den_extra of RPgCheckStr.v at the same commit, for the Tail of the piece
   value_nearest of segment M03 of reac-pw/fuzz_headamp image A: a read-only run, so every byte is the entry's and
   the cut's hs_core is rebuilt from the run's journal alone. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): THE TAIL LANE of the piece value_nearest of segment M03 of LLVMFuzzerTestOneInput
   (0x80bc0), lib/A/HPgM3dBase.v's hv_piece_tail_stmt.
   proves function LLVMFuzzerTestOneInput (reuse search: at ossv/recipes 2d2ff01bb6f2, read by the released-proof
   index v5 built 2026-10-30T13:16:21Z, no released proof of these pieces; the lookup record is in the PR body).

   THE CODE (five instructions and one branch, fuzz_headamp.c:141):
     0x83534  sext.w a0,s4         a0 := the 32-bit sign extension of the value s4
     0x83538  ld t2,0xe0(s1)       t2 := n_ent, from the real-frame cell R+0xe0
     0x8353c  ld t6,0xd8(s1)       t6 := &ent[0] = pp + 0x4014, from R+0xd8
     0x83540  addi t3,zero,5       t3 := Headamp.REFUSE_OUT_OF_RANGE
     0x83544  bltu s2,a0 -> RF 0x83460   (the param's top value s2 is below the value)
     0x83548  CELL                 (not taken)
   No instrumented check and no store: the two loads read the real frame at constant offsets.

   THE PROOF. One entry state at TAIL with the real frame [R, R + 0x120) as one read-only region whose two chunks
   are the cells R+0xd8 and R+0xe0 (env slots 32 and 33 hold their values), the facts on R and the shadow offset,
   and no shadow entry. The engine runs to the `bltu`; the branch is decided on the atoms of s2 and s4
   (hv_U_atom, hv_U_sextw: the unsigned test is the integer test top < val, as 1 <= top <= 0x37 and
   0 <= val <= 255); each side runs on to its cut. Every region is read-only, so the run's memory is the entry's
   (frame_of_read_only) and the cut's hq_base3 is the entry's with the run's journal and registers (hvt_base3);
   the callee-saved registers are untouched (aregs_preserved_of_st_ok), so the value facts carry (hvt_at_carry);
   t6, t2 and t3 are read off the run's last state. The model side is HPgM3dVal.v's hvm_cell_inl / hvm_cell_inr
   with hvm_key_cell and hvm_valid.
   Section hypotheses: none beyond the Section's B and MT. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgCalls HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3dVal HPgM3dBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the entry state's pieces ===================================== *)
(* the one region: the real frame at s1 = R, read only, with the two cells the Tail loads *)
Definition hvt_rgs : list YP09.region :=
  [hv_frame 0 0x120 0 0 [YP09.mkChunk 0xd8 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xe0 (CVal 8 (SOff 33 0))]].

Lemma hvt_mod16 : forall R, R mod 32 = 0 -> R mod 16 = 0.
Proof.
intros R H. pose proof (Z.div_mod R 32 ltac:(lia)) as Hd. rewrite H, Z.add_0_r in Hd. rewrite Hd.
replace (32 * (R / 32)) with ((2 * (R / 32)) * 16) by ring. apply Z.mod_mul. lia.
Qed.

(* the env slot 32 + j holds the j-th extra word [RPgCheckStr.v den_extra] *)
Lemma hvt_extra : forall regs extra j (w : word), nth j extra (Z_to_bv 64 0) = w ->
  sv_denot (Ereg regs extra) (SOff (32 + j) 0) = w.
Proof.
intros regs extra j w Hj. apply bv_eq. rewrite denot_SOff, ew_Ereg_extra, Hj, Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ w) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.

(* an 8-byte cell of a cut (HPgBase.hd_at's LCell form) as a chunk of a region *)
Lemma hvt_chunk : forall E mem base off x (n : nat),
  sv_denot E (SOff n 0) = w64 x ->
  val_mem rsegs mem (base + off) 8 (x mod 2 ^ 64) ->
  YP09.chunk_ok rsegs E mem base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E mem base off x n D V.
apply (chunk_ok_val rsegs E mem base off 8 (SOff n 0) (x mod 2 ^ 64)); [| | cbn; lia | exact V].
- rewrite D. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
- pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as Hm. exact Hm.
Qed.

(* a location whose fact a run that keeps the callee-saved registers and every byte keeps *)
Definition hvt_cs_loc (f : hd_loc * Z) : Prop :=
  match fst f with LReg rr => acallee_saved rr | LCell _ _ => True end.

Lemma hvt_L_cs : forall (cx : hs_scx rsegs) r (L : list (hd_loc * Z)),
  Forall hvt_cs_loc L ->
  Forall hvt_cs_loc (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r ++ L).
Proof.
intros cx r L HL. unfold hq_L_seg, hq_L_frame, hq_L_loopc, hq_L_body. cbn [app].
repeat (apply Forall_cons; [unfold hvt_cs_loc; cbn [fst]; first [exact I | (unfold acallee_saved; lia)] |]).
exact HL.
Qed.

(* a register's value as the denotation of its symbolic value [RPgM02KeyV.v m2k_rsv] *)
Ltac hvt_rsv HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Hr : getr (ms_regs ms) r = sv_denot E e)
by (refine (eq_trans (st_ok_restrict_reg segs H E ss ms r HS) (f_equal (sv_denot E) _)); vm_compute; reflexivity)
end.

(* a run over read-only regions keeps the memory: the run's unrestricted frame_of gives the equation *)
Ltac hvt_mem_eq HM :=
match goal with HFx : frame_of _ ?rs ?m0 ?m1 |- _ =>
  lazymatch m0 with mrestrict _ _ => fail | _ => idtac end;
  pose proof (frame_of_read_only _ rs m0 m1 ltac:(vm_compute; reflexivity) HFx) as HM
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Ltac hvt_kio := first [apply same_io_refl | eapply same_io_trans; [| apply hv_same_io_wvb]; hvt_kio].

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the cut's journal-and-image part at a state the run reached: the run's journal, its registers (sp, gp and tp
   kept), the same bytes *)
Lemma hvt_base3 : forall (cx : hs_scx rsegs) (fx2 : YK11.FPState) r sh ly2 S2 W2 regs2 mem2 md2 regs3 md3,
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem2 md3 (x_k rsegs cx) ->
aregs_preserved regs2 regs3 -> same_io md2 md3 ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs3 mem2 md3.
Proof.
intros cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb HJ3 Hpres Hio3.
destruct Hb as (Hcore & Hrest).
split; [|exact Hrest].
destruct Hcore as (_ & Hr & Hfr & Hperm & Hio & Hmo & HK).
split; [exact HJ3|].
split; [intros r0 Hr0; rewrite <- (Hr r0 Hr0); apply Hpres; unfold acallee_saved; lia|].
split; [exact Hfr|]. split; [exact Hperm|].
split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [exact Hmo | exact HK].
Qed.

(* a cut's value facts at a state with the same bytes and the callee-saved registers kept *)
Lemma hvt_at_carry : forall (cx : hs_scx rsegs) (W2 : world rsegs) mem2 regs2 regs3 L,
aregs_preserved regs2 regs3 -> Forall hvt_cs_loc L ->
hs_at_cx rsegs cx W2 mem2 regs2 L -> hs_at_cx rsegs cx W2 mem2 regs3 L.
Proof.
intros cx W2 mem2 regs2 regs3 L Hpres HL HAT.
unfold hs_at_cx, hs_at in *.
eapply hm_atl_kept; [exact HAT|].
intros f Hf. pose proof (proj1 (Forall_forall _ _) HL f Hf) as Hm.
destruct f as [[rr|b o] z]; unfold hvt_cs_loc in Hm; cbn [fst hm_keeps] in Hm |- *.
- apply Hpres. exact Hm.
- intros i Hi. reflexivity.
Qed.

(* ===================================== the Tail ===================================== *)
Theorem hvt_tail_A : hv_piece_tail_stmt B MT.
Proof.
intros cx POST r ev at0 m HS0 HCELL HRF.
intros fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p val cs keys rf HT.
destruct HT as (Hb3 & HAT & Hfs9 & Hfs18 & Hlive & Hat0 & Hkey & Hcv & Hval & Hpair & Hcsk & Hx).
destruct HS0 as (Hpre & _).
pose proof (hv_stack B cx _ Hpre) as (_ & HR32 & _ & _ & _ & H46 & _).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof hv_wx as Hwx. pose proof hv_segs_low as Hsegs.
pose proof Hb3 as (Hcore & _).
pose proof Hcore as (HJ & _).
clear Hcore.
pose proof (hvm_top_bounds p) as Htop.
(* the value facts the entry state reads *)
assert (HLcs : Forall hvt_cs_loc
  (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r ++
   [(LReg 18, hvm_top p); (LReg 20, val); (LReg 21, Z.of_nat m + 2); (LCell XR 0x98, p); (LCell XR 0xa0, ch)])).
{ apply hvt_L_cs.
  repeat (apply Forall_cons; [unfold hvt_cs_loc; cbn [fst]; first [exact I | (unfold acallee_saved; lia)] |]).
  apply Forall_nil. }
pose proof HAT as HAT'.
unfold hs_at_cx, hs_at, hq_L_seg, hq_L_frame, hq_L_loopc, hq_L_body in HAT'.
cbn [app] in HAT'.
rewrite !Forall_cons_iff in HAT'.
destruct HAT' as (A8 & A9 & A19 & A23 & A22 & A24 & A25 & A26 & A27 &
  C20 & C60 & Ca8 & Cb0 & Cb8 & Cc0 & Ce8 & Cf0 & Cf8 & C100 & C108 & C110 & C118 &
  Cc8 & Cd0 & Cd8 & Ce0 & A18 & A20 & A21 & C98 & Ca0 & _).
cbn [fst snd hd_at hd_xv] in A9, A23, A18, A20, Cd8, Ce0.
clear A8 A19 A22 A24 A25 A26 A27 C20 C60 Ca8 Cb0 Cb8 Cc0 Ce8 Cf0 Cf8 C100 C108 C110 C118 Cc8 Cd0 A21 C98 Ca0.
(* the entry state at TAIL: env slots 32 / 33 = &ent[0] / n_ent *)
set (extra := [w64 (e_pp (x_e rsegs cx) + HQ_ENT0); w64 (hq_nent r)] : list word).
pose proof (hvt_extra regs2 extra 0 (w64 (e_pp (x_e rsegs cx) + HQ_ENT0)) eq_refl) as D32.
pose proof (hvt_extra regs2 extra 1 (w64 (hq_nent r)) eq_refl) as D33.
cbn [Nat.add] in D32, D33.
assert (E9 : bv_unsigned (ew (Ereg regs2 extra) 9) = e_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs2 extra 9 (Z_to_bv 5 9) eq_refl), A9. unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : bv_unsigned (ew (Ereg regs2 extra) 23) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs2 extra 23 (Z_to_bv 5 23) eq_refl), A23. unfold w64, SHADOW_OFF.
  apply unsigned_lit_small. lia. }
assert (Hrs : Forall (region_ok rsegs (Ereg regs2 extra) (mrestrict (w_H W2) mem2)) hvt_rgs).
{ unfold hvt_rgs, hv_frame. apply Forall_cons; [|apply Forall_nil].
  apply (hm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e rsegs cx)) 0 0x120); [exact E9 | lia | lia |].
  apply Forall_cons; [exact (hvt_chunk _ _ _ 0xd8 _ 32 D32 Cd8)|].
  apply Forall_cons; [exact (hvt_chunk _ _ _ 0xe0 _ 33 D33 Ce0)|].
  apply Forall_nil. }
assert (Hpd : pairwise_disjoint (Ereg regs2 extra) hvt_rgs) by exact (conj I I).
assert (HG : facts_ok (Ereg regs2 extra) hv_facts)
  by exact (hv_facts_ok _ (e_R (x_e rsegs cx)) E9 ltac:(lia) (hvt_mod16 _ HR32) E23).
pose proof (hv_entry (fx := fx2) HV_TAIL [] hvt_rgs hv_facts W2 regs2 extra mem2 (Forall_nil _)
  ltac:(vm_compute; reflexivity) Hrs Hpd HG) as HS.
remember (Ereg regs2 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs HV_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (E18 : ew E 18 = Z_to_bv 64 (hvm_top p))
  by (rewrite HE, (ew_Ereg_nat regs2 extra 18 (Z_to_bv 5 18) eq_refl); exact A18).
assert (E20 : ew E 20 = Z_to_bv 64 val)
  by (rewrite HE, (ew_Ereg_nat regs2 extra 20 (Z_to_bv 5 20) eq_refl); exact A20).
clear Hrs Hpd HG.
unfold cfg_at. change (w64 HV_TAIL) with (Z_to_bv 64 HV_TAIL).
(* 0x83534 .. 0x83540, stop at 0x83544 `bltu s2,a0` *)
hv_run hv_awr.
hvt_mem_eq HM1.
hv_branch Hb.
(* Hb: branch_taken BC_LTU (sv_denot E (SOff 18 0)) (sv_denot E (SAluw ALU_ADD (SOff 20 0) (SLit 0))) *)
all: rewrite branch_ltu_U, (hv_U_atom E 18 (hvm_top p) E18 ltac:(lia)),
  (hv_U_sextw E (SOff 20 0) val (hv_U_atom E 20 val E20 ltac:(lia)) ltac:(lia)) in Hb.
- (* 0x83544 taken: top < val, RF 0x83460 with t3 = OUT_OF_RANGE *)
  apply Z.ltb_lt in Hb.
  assert (Hinl : Headamp.expect_cell k v = inl Headamp.REFUSE_OUT_OF_RANGE).
  { apply (hvm_cell_inl k v ch p Hkey). right. rewrite Hcv. exact Hb. }
  hv_run_to hv_awr 0x83460.
  hvt_mem_eq HM2.
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ _) |- _ =>
    hvt_rsv HSx (Z_to_bv 5 31) G31; hvt_rsv HSx (Z_to_bv 5 7) G7; hvt_rsv HSx (Z_to_bv 5 28) G28 end.
  lazymatch goal with HSx : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
    pose proof (aregs_preserved_of_st_ok rsegs H E ss ms regs2 extra HSx HAE ltac:(vm_compute; reflexivity))
      as Hpres3;
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HSx eq_refl);
    replace (ss_pc ss) with 0x83460 by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite HM2, HM1 in HJx end.
  rewrite HM2, HM1.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) ?d) _ =>
    apply (HRF fx2 ly2 S2 W2 rg mem2 d k v Headamp.REFUSE_OUT_OF_RANGE cs keys rf) end.
  unfold hq_cut_RF.
  refine (conj _ (conj _ (conj Hfs9 (conj Hfs18 (conj Hlive (conj Hat0
    (conj Hinl (conj (or_intror eq_refl) (conj Hpair Hx))))))))).
  + lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (hvt_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 _ _ Hb3 HJx Hpres3) end.
    hvt_kio.
  + pose proof (hvt_at_carry cx W2 mem2 regs2 _ _ Hpres3 HLcs HAT) as HATk.
    unfold hs_at_cx, hs_at in HATk |- *.
    rewrite !Forall_app in HATk |- *.
    destruct HATk as (K1 & K2 & K3 & K4).
    split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
    rewrite !Forall_cons_iff in K4. destruct K4 as (_ & _ & K21 & _ & _ & _).
    apply Forall_cons; [cbn [fst snd hd_at]; etransitivity; [exact G31 | exact D32]|].
    apply Forall_cons; [cbn [fst snd hd_at]; etransitivity; [exact G7 | exact D33]|].
    apply Forall_cons; [exact K21|].
    apply Forall_cons; [cbn [fst snd hd_at]; etransitivity; [exact G28 | reflexivity]|].
    apply Forall_nil.
- (* not taken: val <= top, CELL 0x83548 *)
  apply Z.ltb_ge in Hb.
  assert (Hinr : Headamp.expect_cell k v = inr (ch, p, val)).
  { rewrite <- Hcv. apply (hvm_cell_inr k v ch p Hkey); rewrite Hcv; lia. }
  assert (Hvalid : Headamp.cell_valid (ch, p, val)).
  { destruct (hvm_key_cell _ ch p Hkey) as (Hch & Hp). apply (hvm_valid ch p val Hch Hp). lia. }
  hv_run_to hv_awr 0x83548.
  hvt_mem_eq HM2.
  lazymatch goal with HSx : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
    pose proof (aregs_preserved_of_st_ok rsegs H E ss ms regs2 extra HSx HAE ltac:(vm_compute; reflexivity))
      as Hpres3;
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HSx eq_refl);
    replace (ss_pc ss) with 0x83548 by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite HM2, HM1 in HJx end.
  rewrite HM2, HM1.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) ?d) _ =>
    apply (HCELL fx2 ly2 S2 W2 rg mem2 d k v ch p val cs keys rf) end.
  unfold hq_cut_CELL.
  refine (conj _ (conj _ (conj Hfs9 (conj Hfs18 (conj Hlive (conj Hat0
    (conj Hinr (conj Hvalid (conj Hpair (conj Hcsk Hx)))))))))).
  + lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (hvt_base3 cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 _ _ Hb3 HJx Hpres3) end.
    hvt_kio.
  + pose proof (hvt_at_carry cx W2 mem2 regs2 _ _ Hpres3 HLcs HAT) as HATk.
    unfold hs_at_cx, hs_at in HATk |- *.
    rewrite !Forall_app in HATk |- *.
    destruct HATk as (K1 & K2 & K3 & K4).
    split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
    rewrite !Forall_cons_iff in K4. destruct K4 as (_ & K20 & K21 & K98 & Ka0 & _).
    apply Forall_cons; [exact K20|]. apply Forall_cons; [exact K21|].
    apply Forall_cons; [exact K98|]. apply Forall_cons; [exact Ka0|].
    apply Forall_nil.
Qed.

End t.

Print Assumptions hvt_tail_A.
