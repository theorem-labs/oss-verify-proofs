(* lv2_locate_manifest_readings: the shared return at 0x820b4 (mv a0, s5; restore ra, s0..s11 from the frame;
   addi sp, sp, 208; ret): rd_seg_R. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the frame at the return: the saved registers, read only; atoms 32 .. 44 = ra, s0 .. s11 of readings' entry *)
Definition RD_RET_CS : list (Z * nat) :=
  [(200, 0%nat); (192, 1%nat); (184, 2%nat); (176, 3%nat); (168, 4%nat); (160, 5%nat); (152, 6%nat); (144, 7%nat);
   (136, 8%nat); (128, 9%nat); (120, 10%nat); (112, 11%nat); (104, 12%nat)].
Definition ss_rr : sstate :=
  mkSS RD_R sr_atoms [YP09.mkRegion (Some 2%nat) 104 208 104 104 (rd_slot_chunks RD_RET_CS)] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Definition rd_ret_extra (R : bvmap 5 word) : list word := map (fun s => getr R (Z_to_bv 5 (snd s))) RD_SAVED.

Section h. Context {fx : YK11.FPState}.
Lemma rd_ret_reg : forall H E ss ms regs3 extra (r : bv 5) j,
  st_ok tfibsegs E ss (restrict H ms) -> E = Ereg regs3 extra -> sr_get (ss_regs ss) r = SOff (32 + j) 0 ->
  getr (ms_regs ms) r = nth j extra (Z_to_bv 64 0).
Proof.
intros H E ss ms regs3 extra r j HS HE Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. cbn [sv_denot].
subst E. rewrite ew_Ereg_extra, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma rd_ret_atom : forall H E ss ms regs3 extra (r r' : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> E = Ereg regs3 extra -> sr_get (ss_regs ss) r = SOff n 0 ->
  Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs3 r'.
Proof.
intros H E ss ms regs3 extra r r' n HS HE Hr Hn. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr.
cbn [sv_denot]. subst E. rewrite (ew_Ereg_nat regs3 extra n r' Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma rd_saved_chunks : forall E m b R regs3, E = Ereg regs3 (rd_ret_extra R) ->
  Forall (fun s => val_mem tfibsegs m (b + fst s) 8 (bv_unsigned (getr R (Z_to_bv 5 (snd s))))) RD_SAVED ->
  Forall (fun c => val_mem tfibsegs m (b + fst c) 8 (bv_unsigned (ew E (32 + snd c)))) RD_RET_CS.
Proof.
intros E m b R regs3 HE H. subst E. unfold RD_SAVED in H. unfold RD_RET_CS.
repeat (apply Forall_cons_iff in H; destruct H as [?Hx H]).
repeat constructor; cbn [fst snd]; rewrite ew_Ereg_extra; unfold rd_ret_extra; cbn [nth map RD_SAVED snd]; assumption.
Qed.
End h.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).

Theorem rd_ret_holds : rd_seg_R B CTX.
Proof.
intros cx k ly3 S3 W3 regs3 mem3 md3 res HB HC H21 Hres HRF.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
destruct HB as (HAN & _ & _ & _ & _ & _ & _ & Htopr & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HC as (HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFR : STK_readings = 16624) by reflexivity.
set (R := cx_regs cx) in *. set (sp0 := cx_sp cx) in *.
assert (HF : cx_F cx = sp0 - 208) by reflexivity.
set (extra := rd_ret_extra R).
set (E := Ereg regs3 extra).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 208).
{ unfold E. rewrite (ew_Ereg_nat regs3 extra 2 2%bv eq_refl), R2, <- HF. apply unsigned_lit_small.
  unfold cx_F; fold sp0. unfold sp0, cx_sp. fold R. lia. }
assert (HS : st_ok tfibsegs E ss_rr (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 RD_R) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (rd_frame_region_ok E _ (sp0 - 208)); [exact Usp | unfold sp0, cx_sp; fold R; lia | unfold sp0, cx_sp; fold R; lia
      | intros o Ho; lia |].
    unfold rd_saved_ok in HSV. rewrite HF in HSV.
    exact (rd_saved_chunks E _ (sp0 - 208) R regs3 eq_refl HSV).
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    change (ew (Ereg regs3 extra) 2) with (ew E 2). rewrite Usp. change (2 ^ 4) with 16.
    split; [|exact I]. unfold sp0, cx_sp. fold R.
    split; [lia|]. split; [|lia]. replace (spZ R - 208) with (spZ R + (-13) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal16. }
change (unpoison [] mem3) with mem3 in HJ.
unfold cfg_at. change (w64 RD_R) with (Z_to_bv 64 RD_R).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 RD_R) mem3 (seg_rom tfibsegs))) in HJ.
aj_run rd_tbl_ok HS HJ.
{ awr_ok_tac. }
lazymatch goal with H : frame_of E (ss_mem ss_rr) mem3 _ |- _ =>
  pose proof (frame_of_read_only E (ss_mem ss_rr) _ _ eq_refl H) as Hm end.
eapply (SRr_ret_at tfibsegs rd_tbl rd_tbl_ok Hwx W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat2.
assert (G1 : getr (ms_regs ms) 1 = getr R 1).
{ rewrite (rd_ret_reg _ E _ _ regs3 extra 1%bv 0 HS eq_refl ltac:(vm_compute; reflexivity)). reflexivity. }
assert (G2 : getr (ms_regs ms) 2 = getr R 2).
{ rreg HS (2%bv : bv 5) Q2. rewrite Q2. apply bv_eq. rewrite unsigned_lit_small.
  - rewrite Usp. unfold sp0, cx_sp. fold R. unfold spZ. lia.
  - change (ew (Ereg regs3 extra) 2) with (ew E 2). rewrite Usp. unfold sp0, cx_sp. fold R. lia. }
unfold rd_post.
eexists ly3, S3, (ms_regs ms), (ms_mem ms), _, res.
split.
{ rewrite G1. rewrite Hra. reflexivity. }
split.
{ eapply (ajournal_mono_k tfibsegs B); [apply (ajournal_materialize tfibsegs B LAWS Hsegs); exact HJ | lia]. }
split.
{ rewrite Hm. exact K16. }
split.
{ apply g3_aregs; [|exact G2].
  intros r Hr. cbv [G3_KEPT In] in Hr.
  destruct Hr as [<-|[<-|Hr]].
  - rewrite (rd_ret_atom _ E _ _ regs3 extra 3%bv 3%bv 3 HS eq_refl ltac:(vm_compute; reflexivity) eq_refl). exact R3.
  - rewrite (rd_ret_atom _ E _ _ regs3 extra 4%bv 4%bv 4 HS eq_refl ltac:(vm_compute; reflexivity) eq_refl). exact R4.
  - repeat (destruct Hr as [<- | Hr];
      [ match goal with |- getr ?rg ?r = _ =>
          first [ rewrite (rd_ret_reg _ E _ _ regs3 extra r 1 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 2 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 3 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 4 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 5 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 6 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 7 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 8 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 9 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 10 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 11 HS eq_refl ltac:(vm_compute; reflexivity))
                | rewrite (rd_ret_reg _ E _ _ regs3 extra r 12 HS eq_refl ltac:(vm_compute; reflexivity)) ] end;
        cbn [nth extra rd_ret_extra map RD_SAVED snd]; f_equal; apply bv_eq; reflexivity
      | ]).
    destruct Hr. }
split.
{ rewrite (rd_ret_atom _ E _ _ regs3 extra 10%bv 21%bv 21 HS eq_refl ltac:(vm_compute; reflexivity) eq_refl).
  exact H21. }
destruct HRF as (HPm & HNR & HVr).
split; [exact HPm|]. rewrite Hm. split; [exact HNR | exact HVr].
Qed.
End c.
