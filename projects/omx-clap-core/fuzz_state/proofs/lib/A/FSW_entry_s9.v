(* fs program part, lane ENTRY, segment S9 of the LLVMFuzzerTestOneInput walk (fs.asan 0x81110-0x811b0, the epilogue):
   from the canonical boundary fe_ss PC_epi [] (INV_C9) to the return, fe_post. rule 24: no function proved here (fs's
   own harness entry, written in the donor cgif_file_fuzzer's form; `proof-index LLVMFuzzerTestOneInput` covers
   other units' harnesses only).
   The run (one engine run, entry-dis.txt 0x81110-0x811b0): `sb -8, 4(s9)` (the shadow region, atom 25), the header
   magic 0x45e0360e at 0(s8) (the frame region, atom 24), `beqz s2` not taken (s2 re-expressed as the frame atom 24,
   whose fact says >= 4096: the real-stack arm 0x81158-0x81174 is dead), eight f5 shadow stores, `ld a0, 0x38(s2)` (the
   frame's flag word: atom 44), `sb zero, 0(a0)` (the frame release, on the one-byte flag region added at atom 44),
   `j 0x81178`, a0 = 0, sp = s0 - 96, the eleven reloads from the s0 region (atoms 33..43), sp = s0, stopping at `ret`.
   The store run is the kit's FSW_frame.fsw_flag_storeU (a working branch c266b4b4388): its
   continuation gives the journal with own = [] over stack_free_state. The return is YA0o.SRr_ret_at.
   Port-from: the donor's aj_flag_store users (cgif_file_fuzzer lib/A/ACf4.v:76-121 rt_XP: the flag region, the store
   run, SRr_ret_at, the post; YCbq.v aj_flag_store), FSW_ret.v fsw_retU (SRr_ret_at + ajournal_materialize) and FSW_K.v's
   fsw_ret tactic (fsw_preserved for aregs_preserved). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_pstat_store.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
ACfn FSH_Harness FSH_Fn_entry FSW_entry_defs FSW_entry_canon.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the run: the start state is fe_ss PC_epi [] with s2 re-expressed as the frame atom 24 (so `ld a0, 0x38(s2)`
   reads the frame region's flag word) and the fake frame's flag byte as a one-byte region at atom 44 (the flag address,
   fe_extra's 13th atom), in front ---- *)
Definition fe_flag_region : YP09.region := YP09.mkRegion (Some 44%nat) 0 1 0 1 [].
Definition ss9_0 : sstate :=
  mkSS PC_epi (sr_set sr_atoms 18%bv (SOff 24 0)) (fe_flag_region :: fe_regions []) None (ss_facts (fe_ss PC_epi [])).
(* the engine stops at the `ret` (0x811b0, RS_stopped (SR_jalr (SOff 33 0))): ra = atom 33, sp = atom 8, a0 = 0,
   s0 .. s9 = atoms 34 .. 43, the flag byte 0 *)
Definition ss9_1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs entry_tbl FUEL ss9_0).
Definition st9 : run_status := Eval vm_compute in snd (sym_runN tfibsegs entry_tbl FUEL ss9_0).
Lemma ss9_run : sym_runN tfibsegs entry_tbl FUEL ss9_0 = (ss9_1, st9).
Proof. vm_compute. reflexivity. Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.

(* the four statics (fs_glob's cells, in fs.asan's last RW segment [0xa1000, 0x5fd000)) are kept by a memory change
   that keeps that segment's bytes *)
Lemma fe9_glob_kept : forall (W : world tfibsegs) m m' live peak cnt fail,
  (forall a, 0xa1000 <= a < 0x5fd000 -> mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a)) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hs (G1 & G2 & G3 & G4 & R).
assert (VB : forall a v, 0xa1000 <= a -> a + 8 <= 0x5fd000 -> val_mem tfibsegs (mrestrict (w_H W) m) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') a 8 v).
{ intros a v Ha Hb Hv k0 Hk0. unfold mbyte. rewrite (Hs (a + Z.of_nat k0)) by lia. exact (Hv k0 Hk0). }
unfold fs_glob, fs_glob_at in *. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|].
split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|].
split; [apply VB; [lia | lia | exact G4]|].
exact R.
Qed.

Lemma fe_seg9 : fe_from B FS_PSTAT_FP (fe_post B FS_PSTAT_FP) (fe_ss PC_epi []) (INV_C9 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HINV HS.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
destruct HINV as (-> & HPerm & (Hk0 & Hio & _ & _) & HRC & (cnt3 & Hstat3 & Hcnt3)).
destruct HRC as (E8 & _ & _ & E18 & E24 & E25 & E3 & E4 & E26 & E27).
destruct HB as (Hpre & _).
destruct Hpre as (Hafn & Hra & _ & _ & Hpay & _ & _ & HfrS & _).
destruct Hafn as (_ & Hrok & _).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & Hfr3 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
rewrite unpoison_nil in HAR3.
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _). unfold LLVMF_STK in Hslo.
assert (Hin3 : In (0, c_fpos cx) (frames S3)) by (rewrite Hfr3; apply in_or_app; left; left; reflexivity).
assert (ELY : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & H & _); exact H).
assert (EF : frame_addr ly3 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY; reflexivity).
assert (EFL : flag_addr ly3 0 (c_fpos cx) = fe_FL cx) by (unfold fe_FL, flag_addr; rewrite ELY; reflexivity).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
(* the frame, its shadow and its flag (AR's frames / flag / client-image laws at the boundary) *)
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 0 (c_fpos cx) HAR3 Hin3) as (Hal32 & Happ & Hfp & Hsp).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (ms_mem ms3) md3 0 (c_fpos cx) HAR3 Hin3) as (H4096 & Hfc & _).
destruct (al_flag _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 0 (c_fpos cx) HAR3 Hin3) as (Hflp & Hflo & Hflapp & Hflc).
rewrite EF in Hal32, Happ, Hfp, Hsp, H4096, Hfc. rewrite EFL in Hflp, Hflo, Hflapp, Hflc.
rewrite Hfb in Happ, Hfp, Hsp, Hfc. change (64 / 8) with 8 in Hsp.
change (shadow_addr (fe_F cx)) with (fe_SF cx) in Hsp.
assert (HFimg : forall a, fe_F cx <= a < fe_F cx + 64 -> ~ in_img tfibsegs a).
{ intros a Ha. destruct (al_client_img _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 a HAR3) as [_ Hni]; [|exact Hni].
  right. left. exists 0, (c_fpos cx). split; [exact Hin3|]. rewrite EF, Hfb. exact Ha. }
assert (HFLimg : ~ in_img tfibsegs (fe_FL cx)).
{ destruct (al_client_img _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 (fe_FL cx) HAR3) as [_ Hni]; [|exact Hni].
  right. right. exists 0, (c_fpos cx). split; [exact Hin3 | symmetry; exact EFL]. }
destruct Hflapp as [Hfl4096 _].
pose proof (shadow_addr_bounds (fe_F cx) ltac:(unfold kHighMemEnd; lia)) as (Hs1 & Hs2).
change (shadow_addr (fe_F cx)) with (fe_SF cx) in Hs1, Hs2.
unfold kLowMemEnd, kHighShadowEnd in Hs1, Hs2.
(* the env's atoms as numbers *)
assert (U8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite E8; apply wz; lia).
assert (U24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite E24; apply wz; lia).
assert (U25 : bv_unsigned (ew E 25) = fe_SF cx) by (rewrite E25; apply wz; lia).
assert (E44 : ew E 44 = Z_to_bv 64 (fe_FL cx))
  by (change 44%nat with (32 + 12)%nat; rewrite (HE 12%nat) by lia; reflexivity).
assert (U44 : bv_unsigned (ew E 44) = fe_FL cx) by (rewrite E44; apply wz; lia).
(* s2 := the frame atom 24 *)
assert (R18 : YK11.getr (ms_regs (restrict (w_H W3) ms3)) 18%bv = sv_denot E (SOff 24 0)).
{ rewrite (st_ok_reg tfibsegs E _ _ 18%bv HS). change (sr_get (ss_regs (fe_ss PC_epi [])) 18%bv) with (SOff 18 0).
  rewrite !fsw_SOff0, E18, E24. reflexivity. }
pose proof (st_ok_set_reg tfibsegs E _ _ 18%bv (SOff 24 0) HS
  ltac:(intros Hc; apply (f_equal bv_unsigned) in Hc; discriminate Hc) R18) as HS1.
(* the flag byte as a region at atom 44 *)
assert (HS2 : st_ok tfibsegs E ss9_0 (restrict (w_H W3) ms3)).
{ refine (st_ok_add_region' tfibsegs E _ _ fe_flag_region HS1 ltac:(vm_compute; reflexivity) _ _).
  - unfold region_ok, fe_flag_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U44. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (fe_FL cx + o) with (fe_FL cx) by lia. apply (apresent_writable tfibsegs). exact Hflp.
  - change (all_disjoint E fe_flag_region (fe_regions [])).
    unfold fe_regions, fe_flag_region, fe_frame_region, fe_shadow_region, fs_ret_s0_region.
    cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U44, U24, U25, U8.
    split; [|split; [|split; [|exact I]]].
    + destruct (Z_lt_ge_dec (fe_FL cx) (fe_F cx)); [left; lia|].
      destruct (Z_lt_ge_dec (fe_FL cx) (fe_F cx + 64)); [exfalso | right; lia].
      destruct (Hfp (fe_FL cx) ltac:(lia)) as (_ & Hno). exact (Hno Hflo).
    + destruct (Z_lt_ge_dec (fe_FL cx) (fe_SF cx)); [left; lia|].
      destruct (Z_lt_ge_dec (fe_FL cx) (fe_SF cx + 8)); [exfalso | right; lia].
      destruct (Hsp (fe_FL cx - fe_SF cx) ltac:(lia)) as (_ & Hno).
      replace (fe_SF cx + (fe_FL cx - fe_SF cx)) with (fe_FL cx) in Hno by lia. exact (Hno Hflo).
    + left. lia. }
(* the store run, through the flag release *)
refine (FSW_frame.fsw_flag_storeU B ML ASF FFL entry_tbl entry_tbl_ok W3 FUEL E ss9_0 ss9_1 st9 ms3 LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP
  (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly3 S3 [] md3 k 0 (c_fpos cx) (fe_post B FS_PSTAT_FP cx)
  HS2 ss9_run I HJ HARU ltac:(lia) _ _ _).
- (* every byte the run may write: the s0 window (stack), the frame and its shadow (own frame), the flag *)
  intros a (r & Hr & Ha). unfold ss9_0 in Hr. cbn [ss_mem] in Hr. unfold fe_regions in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
    unfold fe_flag_region, fe_frame_region, fe_shadow_region, fs_ret_s0_region in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  + rewrite U44 in Ha. right. rewrite EFL. lia.
  + rewrite U24 in Ha. left. left. right; right; right. exists 0, (c_fpos cx). split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. lia.
  + rewrite U25 in Ha. left. left. right; right; right. exists 0, (c_fpos cx). split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. change (64 / 8) with 8.
    change (shadow_addr (fe_F cx)) with (fe_SF cx). lia.
  + rewrite U8 in Ha. left. left. left. unfold LLVMF_STK. lia.
- (* the run leaves the flag byte 0 *)
  intros msr HSr.
  pose proof (fsw_region_nth E ss9_1 msr 0
    (YP09.mkRegion (Some 44%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HSr ltac:(vm_compute; reflexivity)) as HR.
  pose proof (fsw_field E (ms_mem msr) 44 (fe_FL cx) _ 0 1 0 1 0 1%N (SLit 0) 0 HR U44 (or_introl eq_refl)
    ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0.
  replace (fe_FL cx + 0 + Z.of_nat 0) with (fe_FL cx) in V0 by lia.
  rewrite EFL, V0. reflexivity.
- (* after the store: the return *)
  intros ms' mat' HS' HJ' HARU' HF HFr HG.
  eapply (SRr_ret_at tfibsegs _ entry_tbl_ok fs_wx W3 E ss9_1);
    [exact HS' | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros mat2.
  assert (Rra : YK11.getr (ms_regs ms') 1%bv = YK11.getr (c_regs cx) 1%bv).
  { rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E ss9_1 ms' 1%bv HS').
    change (sr_get (ss_regs ss9_1) 1%bv) with (SOff 33 0). rewrite fsw_SOff0.
    change 33%nat with (32 + 1)%nat. rewrite (HE 1%nat) by lia. reflexivity. }
  pose proof (fsw_reg_lit (w_H W3) E ss9_1 ms' 10%bv 0 HS' ltac:(vm_compute; reflexivity) ltac:(lia)) as Ra0.
  pose proof (ajournal_materialize tfibsegs _ LAWS fs_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ') as HJf.
  rewrite unpoison_nil in HJf.
  unfold fe_post. cbv beta.
  lazymatch type of HJf with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ ?mdx _ =>
    exists lyx, Sx, (ms_regs ms'), (ms_mem ms'), mdx, k, cnt3 end.
  split.
  { unfold cfg_at. rewrite Rra. unfold YK0s.ret_ok in Hrok. rewrite Hrok.
    unfold w64. rewrite <- Hra. unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact HJf|].
  split; [unfold EV_check_no_overread, EV_preset_base64_decode, EV_check_as_written, EV_check_round_trip, EV_LIB in *;
    lia|].
  split.
  { apply (fsw_preserved (w_H W3) E ss9_1 ms' (c_regs cx) (fun r => sr_get (ss_regs ss9_1) r) HS');
      [vm_compute; reflexivity|].
    intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]; cbv beta;
    lazymatch goal with |- sv_denot _ (sr_get (ss_regs ss9_1) ?q) = _ =>
      let e := eval vm_compute in (sr_get (ss_regs ss9_1) q) in change (sr_get (ss_regs ss9_1) q) with e end;
    rewrite fsw_SOff0;
    first
    [ exact E3 | exact E4 | exact E26 | exact E27
    | rewrite E8; unfold fe_sp0, spZ; apply Z_to_bv_bv_unsigned
    | lazymatch goal with |- ew E ?n = _ =>
        let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat; rewrite (HE j) by lia; reflexivity end ]. }
  split; [exact Ra0|].
  split.
  { change (ablocks B ly3 (stack_free_state 0 (c_fpos cx) S3)) with (ablocks B ly3 S3). exact HPerm. }
  split.
  { apply (same_io_trans _ md3); [exact Hio|].
    apply (same_io_trans _ (with_vm_backing (m_vm_lazy md3) mat' md3)).
    - apply same_io_materialized. apply same_but_materialized_wvb_any.
    - apply same_io_materialized. apply same_but_materialized_wvb_any. }
  split.
  { (* the payload: a block of the entry, not in the footprint (the statics are image bytes, a block is not) *)
    intros i Hi. destruct Hpay as [(Hn0 & _) | (Hn & Hinb)]; [lia|].
    pose proof HJf as (HARf & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    assert (Hinf : In (c_p cx, c_n cx) (ablocks B ly3 (stack_free_state 0 (c_fpos cx) S3))).
    { change (ablocks B ly3 (stack_free_state 0 (c_fpos cx) S3)) with (ablocks B ly3 S3).
      apply (Permutation_in _ (Permutation_sym HPerm)). exact Hinb. }
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hreq).
    apply (F2 (c_p cx) (c_n cx) i Hinb Hinf ltac:(lia)).
    intros Hfp'. pose proof (pstat_bounds _ Hfp') as Hb.
    destruct (al_client_img _ _ LAWS ly3 _ W3 _ _ (c_p cx + i) HARf) as [_ Hni].
    { left. exists (c_p cx), (c_n cx). split; [exact Hinf | lia]. }
    exact (Hni (fs_rw3_img _ Hb)). }
  split.
  { (* the statics: the run writes none of them *)
    destruct Hstat3 as (peak & Hg). exists peak.
    apply (fe9_glob_kept W3 (ms_mem ms3)); [|exact Hg].
    intros a Ha. apply HFr. rewrite unsigned_lit_small by lia.
    intros (r & Hr & Hra'). unfold ss9_0 in Hr. cbn [ss_mem] in Hr. unfold fe_regions in Hr.
    pose proof (fs_rw3_img a Ha) as Hai.
    destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
      unfold fe_flag_region, fe_frame_region, fe_shadow_region, fs_ret_s0_region in Hra';
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'.
    - rewrite U44 in Hra'. apply HFLimg. replace (fe_FL cx) with a by lia. exact Hai.
    - rewrite U24 in Hra'. exact (HFimg a ltac:(lia) Hai).
    - rewrite U25 in Hra'. lia.
    - rewrite U8 in Hra'. lia. }
  exact Hcnt3.
Qed.
End s.


