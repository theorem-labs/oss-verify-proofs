(* fuzz_preset, slice S5b, image A: parse_value's REFUSAL JOIN (listing rows 326..328, A 0x86420..0x86428: `addi a0,
   zero, -8`, `sb a0, 4(s8)`, `j` to the shared epilogue at row 225) with a memory invariant P carried across the run.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma / runner invariant twin).
   WHAT: vrd_ref_join_P, VrdNum.vrd_ref_join (lib/A/VrdNum.v) with the generic binder P : (word -> option byte) -> Prop,
   its laws srr_inv_laws segs P (YSRrMemnorm.v, a working branch a7b940285d0, blob 8bf0942a10ca), P of the
   memory at entry and P of the memory at the join as a conjunct of the continuation. ONE copy (a Theorem Labs lane's ruling,
   2026-10-29): every arm that reaches row 326 cites it (number, container, string, literal). Its instance is the
   memnorm keep from parse_value's entry memory: P := fun m => YAkMemnorm.memnorm segs mem0 -> YAkMemnorm.memnorm segs m,
   laws YSRrMemnorm.srr_inv_laws_imp .. (srr_inv_laws_memnorm_k segs).
   HOW: vrd_ref_join's proof, with the one run (YC1fPx.paj_run_to_x) replaced by its P twin YSRrMemnorm.paj_run_to_x_inv
   and the tactic paj_run_to_tok_x by paj_run_to_tok_x_inv; the run's post gives P of the join memory (HPM). Nothing
   is re-walked: the symbolic state, the write premise and the join facts are vrd_ref_join's (VrdNum.vrd_st_ref).
   SECTION HYPOTHESIS: LAWS (the engine's laws), as vrd_ref_join. Numerals: those of vrd_ref_join (64, 8, 4, 2 ^ 44,
   2 ^ 46, 2 ^ 64: LENGTH; the listing rows 225 / 326 via VrdNum.vrd_row). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a YK0j YN3v YG0s YP07 YP0a YG0p YP0d YP0c YC80 YImgTop YC1fP YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog VrdPro VrdNum.
Import ListNotations.
Local Open Scope Z_scope.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.

(* rows 326..328 with P: the state at the join, the arm's own result carried through the one shadow byte they write,
   and P of the join memory. The join state's journal is at the empty budget (the number arm stores no wild trace),
   which every cursor set's wbudget CW 0 admits (VrdNum.vrd_epi_a at the kit's cut 7cdbb61b5fa0) *)
Lemma vrd_ref_join_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c,
  vrd_sh_frame ARx RQ ->
  vrd_ref_a B ARx SK d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c ->
  P (ms_mem (cfg_ms c)) ->
  SRr segs W c (fun W' c' => vrd_epi_a B ARx SK fx d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W' c' /\
                             P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c HRQfr
  (regs & mem & md & ly & S & Hp & k & -> & HJ & HWIN & R8 & R18 & R26 & R24 & R21 & R3 & R4 & Hra & HSAV & HFLAG
   & HinF & HFZ & HE0 & HRQ0) HPM.
change (P mem) in HPM.
pose proof (vrd_stk_nonneg d) as HSTK.
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTACK & _).
pose proof HSTACK as (_ & _ & Hclo & Hlo & Hhi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (HF0 & HFc & HFapp).
destruct (alx_frames segs B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (_ & _ & _ & HFsh).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
rewrite Hfb in HFc, HFsh.
assert (HD8 : 0 <= frame_addr ly 0 pos / 8 <= alloc_ceiling / 8).
{ split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]. }
assert (HAC8 : alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
assert (Hb24 : bv_unsigned (getr regs 24) = SHADOW_OFF + frame_addr ly 0 pos / 8)
  by (rewrite R24; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (Hi4 : 0 <= 4 < 64 / 8) by (replace (64 / 8) with 8 by reflexivity; lia).
assert (Hw24 : writable_at segs (rdW W mem) (SHADOW_OFF + frame_addr ly 0 pos / 8 + 4)).
{ apply (apresent_writable segs). replace (SHADOW_OFF + frame_addr ly 0 pos / 8 + 4)
    with (shadow_addr (frame_addr ly 0 pos) + 4) by (unfold shadow_addr; lia).
  exact (proj1 (HFsh 4 Hi4)). }
pose proof (vrd_st_ref W regs mem _ Hb24 ltac:(unfold SHADOW_OFF in *; lia) Hw24) as HS.
unfold cfg_at. rewrite vrd_pc_ref.
assert (E24 : ew (vrd_E regs) 24 = getr regs 24)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
assert (HEI : img_env VAL A_LIM (vrd_E regs)) by (unfold vrd_E; apply Eimg_env).
assert (SHOK : sh_ok segs vrd_Bx0 (@nil shent) (vrd_E regs) (rdW W mem)) by (apply Forall_nil).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan0 (vrd_row 225).
- (* the write premise: the only window is the frame's own shadow granule *)
  intros a Ha. destruct Ha as (r & Hin & Hr). cbn [vrd_ref_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite E24, Hb24 in Hr.
  right; right; right. exists 0, pos. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Hfb. lia.
- (* the state at the join *)
  pmkst HS.
  prreg HS (8%bv : bv 5) P8. prreg HS (18%bv : bv 5) P18. prreg HS (26%bv : bv 5) P26.
  prreg HS (24%bv : bv 5) P24. prreg HS (21%bv : bv 5) P21. prreg HS (3%bv : bv 5) P3.
  prreg HS (4%bv : bv 5) P4.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
    assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < kHighShadowEnd) ->
              aview segs (w_H W) mT a = aview segs (w_H W) mem a)
  end.
  { intros a Ha64 Ha. unfold aview. f_equal. unfold mbyte.
    rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). cbn [vrd_ref_regions In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E24, Hb24 in Hr.
    rewrite unsigned_lit_small in Hr by exact Ha64.
    apply Ha. unfold kHighShadowEnd, SHADOW_OFF in *. lia. }
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  assert (HKLS : kLowShadowBeg = 2147446784) by reflexivity.
  assert (KV : forall a (n : nat) vv, val_mem segs (rdW W mem) a n vv ->
     spZ regs0 - 104 <= a -> a + Z.of_nat n <= spZ regs0 -> val_mem segs (rdW W (ms_mem ms)) a n vv).
  { intros a n vv Hv Ha1 Ha2. eapply val_mem_kept; [|exact Hv]. intros kk Hk.
    apply HKEEP; lia. }
  assert (HFband : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 ->
     0 <= a < 2 ^ 64 /\ ~ (SHADOW_OFF <= a < kHighShadowEnd)).
  { unfold in_app, ASAN_CEIL in HFapp. rewrite Hfb in HFapp.
    destruct HFapp as (HF4096 & [Hlow | [Hhigh1 Hhigh2]]); intros a Ha; split; lia. }
  apply SRr_ret. split; [|exact HPM].
  exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md), ly, S, Hp, k.
  split; [rewrite vrd_pc_epi; reflexivity|].
  split; [exists []; split; [exact HJ | exact (le_n 0)]|].
  split.
  { intros a Ha Hn. rewrite HKEEP by (unfold kHighShadowEnd, SHADOW_OFF in *; lia).
    exact (HWIN a Ha Hn). }
  split; [rewrite P8; exact R8|].
  split; [rewrite P18; exact R18|].
  split; [rewrite P26; exact R26|].
  split; [rewrite P24; exact R24|].
  split; [rewrite P21; exact R21|].
  split; [rewrite P3; exact R3|].
  split; [rewrite P4; exact R4|].
  split; [exact Hra|].
  split.
  { unfold vrd_saved in HSAV |- *.
    destruct HSAV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
    repeat split; (eapply KV; [eassumption | cbn; lia | cbn; lia]). }
  split.
  { eapply val_mem_kept; [|exact HFLAG]. intros kk Hk.
    destruct (HFband (frame_addr ly 0 pos + 56 + kk) ltac:(lia)) as [Hr1 Hr2].
    apply HKEEP; [exact Hr1 | exact Hr2]. }
  split; [exact HFZ|].
  split; [intros rr; reflexivity|].
  exact (HRQfr ly S Hp W mem (ms_mem ms) md HAR HKEEP HG HRQ0).
Qed.

End r.
