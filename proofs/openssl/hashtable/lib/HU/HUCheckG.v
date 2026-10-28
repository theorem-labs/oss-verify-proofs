(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec StoreOk Hoare ShapeAlg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore
  AsanNodesIO AsanNodesArg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxPlanSound2 CxPlanSoundSums CxNodesIface CxNodesMmA CxNodesMmB
  CxNodesIOSound CxNodesArgSound CxNodesEmitSound CxAcctNoLazy CxBits CxJoinM CxRezero CxRefront.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable HUSumsSpecs HUStdioDefs HUStdioWriteR H0Sinv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition g0_XN (NX : nat) (LIM : Z) : nat -> list expr -> acs -> option acs := fun id args cs =>
  match id with
  | 16%nat => ION.node_ioctl HSEGS cs
  | 30%nat => CAP.node_mmap_p HSEGS H0T NX LIM cs
  | 31%nat => CAP.node_munmap_p HSEGS cs
  | 32%nat => CAP.node_mmap_q HSEGS H0T NX LIM cs
  | 33%nat => node_bitspell args cs
  | 34%nat => node_joinx_m HSEGS NX args cs
  | 35%nat => node_join_alt HSEGS args cs
  | 36%nat => node_join_zero args cs
  | 37%nat => node_rezero args cs
  | 38%nat => node_refront args cs
  | _ => None
  end.
Definition g0_XE (NX : nat) : nat -> list expr -> acs -> option (Z * list spiece * acs) := AN.xe HSEGS H0T NX.
Definition g0_XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.


Section G0Check.
  Variable NX : nat.
  Hypothesis NX_ge : (NX0t <= NX)%nat.
  Hypothesis NX_spw : CAP.expr_vars_lt NX e_spw = true.
  Variable PHI : env -> Prop.
  Hypothesis PHI_agree : forall E E', env_agree NX E E' -> PHI E -> PHI E'.
  Variable sp : word.
  Variable STR0 : Z.
  Variable LIM : Z.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.

  #[local] Notation ISP := (bv_unsigned sp).
  Definition SINVg (E : env) (M : word -> option byte) : Prop := SINVt ISP STR0 E M /\ PHI E.
  #[local] Notation SINV := SINVg.
  #[local] Notation argH := (argHt STR0).

  Lemma usp_lo : 0x7fff80000000 <= ISP. Proof. destruct Hsp as [H _]. exact H. Qed.
  Let AH := argHt_high ISP STR0 usp_lo Hstr.
  Lemma AA_g : forall E E' (a : word), env_agree NX E E' -> argH E a = argH E' a. Proof. reflexivity. Qed.
  Lemma SF_g : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact (SINVt_frame ISP STR0 usp_lo Hstr E M M' Hf H1) | exact H2]. Qed.
  Lemma env_agree_NX0t : forall E E', env_agree NX E E' -> env_agree NX0t E E'.
  Proof. intros E E' H. eapply env_agree_le; [exact H | exact NX_ge]. Qed.
  Lemma SA_g : forall E E' M, env_agree NX E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M Hag [H1 H2]. split; [exact (SINVt_agree ISP STR0 E E' M (env_agree_NX0t E E' Hag) H1) | exact (PHI_agree E E' Hag H2)]. Qed.
  Lemma SP_g : forall E M, SINV E M -> uE E e_pgsp = pgdown ISP.
  Proof. intros E M [H _]. exact (SINVt_pgsp ISP STR0 E M H). Qed.

  Let AA := AA_g. Let SF := SF_g. Let SA := SA_g. Let SP := SP_g.
  (* [comment removed for export] *)
  Lemma ob_sys : forall y, sys_stmt HSEGS H0T NX LIM SINV argH ISP fs y.
  Proof.
    apply (CxNodesMmB.node_sys_sound HSEGS H0T NX LIM SINV argH ISP fs);
      auto using h0t_res_len, h0t_hull_ok, h0t_shadow_ok, h0t_zone_ok, NX_spw.
  Qed.
  Lemma ob_brk2 : brk2_stmt HSEGS H0T NX LIM SINV argH ISP fs.
  Proof.
    apply (CxNodesMmB.node_brk2_sound HSEGS H0T NX LIM SINV argH ISP fs);
      auto using h0t_in_hull, h0t_res_hull, h0t_hull_ok, h0t_shadow_ok, h0t_zone_ok, NX_spw, h0t_res_len, h0t_res_cover, h0t_hull_ne.
  Qed.
  Lemma ob_mmap2 : mm2_stmt HSEGS H0T NX LIM SINV argH ISP fs (node_mmap2 H0T NX LIM).
  Proof.
    apply (node_mmap2_sound_OBL HSEGS H0T NX LIM SINV argH ISP fs);
      auto using h0t_in_hull, h0t_res_len, h0t_res_hull, h0t_hull_ok, h0t_shadow_ok, h0t_zone_ok, NX_spw, h0t_res_cover, h0t_hull_ne.
  Qed.
  Lemma ob_mmapin : forall hole : bool, mm3_stmt HSEGS H0T NX LIM SINV argH ISP fs (node_mmapin H0T LIM hole).
  Proof.
    apply (node_mmapin_sound_OBL HSEGS H0T NX LIM SINV argH ISP fs);
      auto using h0t_in_hull, h0t_res_len, h0t_res_hull, h0t_hull_ok, h0t_shadow_ok, h0t_zone_ok, NX_spw, h0t_res_cover, h0t_hull_ne.
  Qed.
  Lemma ob_mprotect2 : mm2_stmt HSEGS H0T NX LIM SINV argH ISP fs (node_mprotect2 H0T LIM).
  Proof.
    apply (node_mprotect2_sound_OBL HSEGS H0T NX LIM SINV argH ISP fs);
      auto using h0t_in_hull, h0t_res_len, h0t_res_hull, h0t_hull_ok, h0t_shadow_ok, h0t_zone_ok, NX_spw, h0t_res_cover, h0t_hull_ne.
  Qed.
  Lemma ob_exit : exit_stmt HSEGS H0T LIM SINV argH ISP fs.
  Proof. apply (CxNodesMmB.node_exit_sound HSEGS H0T LIM SINV argH ISP fs). Qed.
  Lemma ob_join : join_stmt HSEGS H0T NX LIM SINV argH ISP fs.
  Proof. apply (node_join_sound HSEGS H0T NX LIM SINV argH ISP fs). Qed.
  Lemma ob_joinx : joinx_stmt HSEGS H0T NX LIM SINV argH ISP fs.
  Proof. apply (node_joinx_sound HSEGS H0T NX LIM SINV argH ISP fs); auto using NX_spw. Qed.

  (* [comment removed for export] *)
  Lemma ob_x : forall x, x_on H0T x = true -> x_stmt HSEGS H0T NX LIM SINV argH ISP fs x.
  Proof.
    intros [ | | | | | | | | | | ] Hon; try (cbv in Hon; discriminate Hon).
    - exact (APSX.node_x_sound_XMemset HSEGS H0T NX LIM h0t_segs_wx h0t_in_hull h0t_hull_ok SINV argH ISP
               AH NX_spw AA SF SA fs h0_fill_spec_memset).
    - exact (APSX.node_x_sound_XMemcpy HSEGS H0T NX LIM h0t_segs_wx h0t_in_hull h0t_hull_ok SINV argH ISP
               AH NX_spw AA SF SA fs h0_segs_wr h0_copy_spec_memcpy).
  Qed.

  (* [comment removed for export] *)
  Lemma SINVt_vals : forall E M, SINV E M ->
    uE E e_sp0 = ISP /\ uE E e_str0 = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 (Z.of_nat (length (@nil byte)))
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 1 /\ edenot E (EVar V_L1) = Z_to_bv 64 (Z.of_nat (length (@nil byte)))
    /\ eb E 1%nat = [] /\ eb E 2%nat = [].
  Proof. intros E M [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & _) _]. cbn [length Z.of_nat]. tauto. Qed.

  Lemma SINVt_str : forall E M i j, SINV E M -> CxNodesArgSound.arg_ok 1 i -> (j <= length (CxNodesArgSound.ARG [] [] i))%nat ->
    M (Z_to_bv 64 (CxNodesArgSound.STR STR0 [] i + Z.of_nat j)) = Some (CatExec.byte_at (CxNodesArgSound.ARG [] [] i) j).
  Proof.
    intros E M i j [(_ & _ & _ & _ & _ & _ & _ & _ & H9) _] Hi Hj. destruct i as [|i]; [|cbn in Hi; lia].
    cbn [CxNodesArgSound.ARG length] in Hj. assert (j = 0%nat) by lia. subst j.
    cbn [CxNodesArgSound.STR CxNodesArgSound.ARG Z.of_nat]. rewrite Z.add_0_r. exact H9.
  Qed.

  Lemma Lay_t : 0x7fff80000000 <= ISP /\ ISP + 192 <= STR0 /\ STR0 + Z.of_nat (length (@nil byte)) + 1 <= STR0 + 8
                   /\ (2 <= 1 -> STR0 + Z.of_nat (length (@nil byte)) + 1 + Z.of_nat (length (@nil byte)) + 1 <= STR0 + 8)
                   /\ (STR0 + 8) mod 8 = 0 /\ STR0 + 8 + 16 <= 2 ^ 47 /\ Z.of_nat (length (@nil byte)) <= 131071
                   /\ Z.of_nat (length (@nil byte)) <= 131071 /\ 1 <= 1 <= 1024.
  Proof. pose proof usp_lo. cbn [length Z.of_nat]. repeat split; try lia. rewrite <- Z.add_mod_idemp_l, Hstr8 by lia. reflexivity. Qed.

  Lemma stdio_h0 : forall (H : word -> bool) regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
    H_off_segments HSEGS H -> lazy_all_hidden H model ->
    range_avoids H (Z_to_bv 64 (su - 112)) 112 -> range_avoids H (Z_to_bv 64 wb) (length pending) -> range_avoids H s (length extra) ->
    getr regs 2%bv = Z_to_bv 64 su -> getr regs 10%bv = Z_to_bv 64 f -> getr regs 11%bv = s -> getr regs 12%bv = l -> getr regs 1%bv = ret ->
    4294967296 + 112 <= su -> su <= 0x800000000000 ->
    store_ok HSEGS mem (Z_to_bv 64 (su - 112)) 112 = true ->
    AN.g_file_lo (AN.argtab_of H0T) <= f -> f + 232 <= AN.g_file_hi (AN.argtab_of H0T) ->
    rdn HSEGS mem (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wp)) ->
    rdn HSEGS mem (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wb)) ->
    rdn HSEGS mem (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
    rdn HSEGS mem (Z_to_bv 64 (f + 88)) 8 = Some (word_to_le_bytes 8 bufp) ->
    rdn HSEGS mem (Z_to_bv 64 (f + 96)) 8 = Some (word_to_le_bytes 8 bufsz) ->
    rdn HSEGS mem (Z_to_bv 64 (AN.g_canary_got (AN.argtab_of H0T))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (AN.g_canary (AN.argtab_of H0T)))) ->
    rdn HSEGS mem (Z_to_bv 64 (AN.g_canary (AN.argtab_of H0T))) 8 = Some (word_to_le_bytes 8 can) ->
    0 < fd < 2147483648 ->
    fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_halted model = None ->
    0 <= wb <= wp -> wp <= 2 ^ 47 -> wp - wb = Z.of_nat (length pending) -> bv_unsigned l = Z.of_nat (length extra) ->
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    (wp <= su - 112 \/ su <= wb) -> (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s) ->
    bv_unsigned s + bv_unsigned l <= 2 ^ 47 ->
    rdn HSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending -> rdn HSEGS mem s (length extra) = Some extra ->
    ret_ok ret -> K [] ->
    (forall regs' mem',
       getr regs' 10%bv = l -> getr regs' 2%bv = Z_to_bv 64 su -> getr regs' 1%bv = ret ->
       getr regs' 8%bv = getr regs 8%bv -> getr regs' 9%bv = getr regs 9%bv ->
       getr regs' 18%bv = getr regs 18%bv -> getr regs' 19%bv = getr regs 19%bv -> getr regs' 20%bv = getr regs 20%bv ->
       getr regs' 21%bv = getr regs 21%bv -> getr regs' 22%bv = getr regs 22%bv -> getr regs' 23%bv = getr regs 23%bv ->
       getr regs' 24%bv = getr regs 24%bv -> getr regs' 25%bv = getr regs 25%bv -> getr regs' 26%bv = getr regs 26%bv ->
       getr regs' 27%bv = getr regs 27%bv -> getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
       (forall x : word, ~ (su - 112 <= bv_unsigned x < su) -> ~ (f + 32 <= bv_unsigned x < f + 48) ->
                          ~ (f + 56 <= bv_unsigned x < f + 64) -> mem' x = mem x) ->
       mem_grows mem mem' ->
       rdn HSEGS mem' (Z_to_bv 64 (f + 32)) 8 = Some (word_to_le_bytes 8 (v_add bufp bufsz)) ->
       rdn HSEGS mem' (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 bufp) ->
       rdn HSEGS mem' (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 bufp) ->
       crz HSEGS (mkCfg (mkst regs' ret mem' (seg_rom HSEGS)) model) K) ->
    crz HSEGS (mkCfg (mkst regs (Z_to_bv 64 (AN.g_stdio_write (AN.argtab_of H0T))) mem (seg_rom HSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
  Proof.
    intros H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
           HH HL AVF AVP AVE Hsp' Ha0 Ha1 Ha2 Hra SUlo SUhi SOK0 Flo Fhi Fwp Fwb Ffd Fbuf Fbsz C1 C2 FD Hfd Hh WBP WPhi
           LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
    replace (Z_to_bv 64 (AN.g_stdio_write (AN.argtab_of H0T))) with (0x2b55ac%bv : word) by (apply bv_eq; reflexivity).
    apply (h0_stdio_write_s H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K); try assumption; try (cbn in *; lia).
    - constructor; assumption.
    - split; [exact C1 | exact C2].
    - intros regs' mem' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      apply (HK regs' mem'); assumption.
  Qed.

  Lemma Gro_h0 : img_lo H0T <= AN.g_ro_lo (AN.argtab_of H0T) /\ AN.g_ro_hi (AN.argtab_of H0T) <= img_hi H0T.
  Proof. cbv. split; discriminate. Qed.
  Lemma Gfile_h0 : img_lo H0T <= AN.g_file_lo (AN.argtab_of H0T) /\ AN.g_file_hi (AN.argtab_of H0T) <= img_hi H0T
                   /\ img_lo H0T <= AN.g_canary_got (AN.argtab_of H0T) /\ AN.g_canary_got (AN.argtab_of H0T) + 8 <= img_hi H0T
                   /\ img_lo H0T <= AN.g_canary (AN.argtab_of H0T) /\ AN.g_canary (AN.argtab_of H0T) + 8 <= img_hi H0T.
  Proof. cbv. repeat split; discriminate. Qed.

  Theorem g0_XE_sound : emit_stmt HSEGS H0T NX LIM (g0_XE NX) SINV argH ISP fs.
  Proof.
    pose proof Lay_t as LAY.
    eapply (xe_sound HSEGS H0T NX LIM SINV argH fs h0t_in_hull h0t_hull_ok ISP AH NX_spw AA SF SA
             (Z_to_bv 32 0) (Z_to_bv 32 0) (Z_to_bv 32 0) (Z_to_bv 32 0) (Z_to_bv 32 0) (Z_to_bv 32 0) (Z_to_bv 32 0));
      [cbn; lia | repeat split; reflexivity | exact LAY | exact SINVt_vals | exact SINVt_str | reflexivity | exact Gro_h0 | exact stdio_h0 | exact Gfile_h0].
  Qed.

  (* [comment removed for export] *)
  Theorem g0_XN_sound : ext_stmt HSEGS H0T NX LIM (g0_XN NX LIM) SINV argH ISP fs.
  Proof.
    intros id args. unfold g0_XN.
    do 16 (destruct id as [|id]; [intros cs cs' E R FULL model T _ _ Hn; discriminate Hn|]).
    destruct id as [|id]; [exact (node_ioctl_sound HSEGS H0T NX LIM SINV argH fs ISP SF sp [[]] [])|].
    do 13 (destruct id as [|id]; [intros cs cs' E R FULL model T _ _ Hn; discriminate Hn|]).
    destruct id as [|id].
    { exact (CxNodesMmA.node_mmap_p_sound HSEGS H0T NX LIM SINV argH ISP fs h0t_in_hull h0t_res_len h0t_hull_ok h0t_shadow_ok AH h0t_zone_ok NX_spw AA SF SA SP h0t_res_cover h0t_hull_ne). }
    destruct id as [|id].
    { exact (CxNodesMmB.node_munmap_p_sound HSEGS H0T NX LIM SINV argH ISP h0t_res_len h0t_hull_ok h0t_shadow_ok fs AH SF). }
    destruct id as [|id].
    { exact (CxNodesMmA.node_mmap_q_sound HSEGS H0T NX LIM SINV argH ISP fs h0t_in_hull h0t_res_len h0t_hull_ok h0t_shadow_ok AH h0t_zone_ok NX_spw AA SF SA SP h0t_res_cover h0t_hull_ne). }
    destruct id as [|id].
    { exact (node_bitspell_sound HSEGS H0T NX LIM SINV argH ISP fs args). }
    destruct id as [|id].
    { apply (node_joinx_m_sound HSEGS H0T NX LIM SINV argH ISP fs); auto using NX_spw. }
    destruct id as [|id].
    { exact (node_join_alt_sound HSEGS H0T NX LIM SINV argH ISP fs args). }
    destruct id as [|id].
    { exact (node_join_zero_sound HSEGS H0T NX LIM SINV argH ISP fs args). }
    destruct id as [|id].
    { exact (node_rezero_sound HSEGS H0T NX LIM SINV argH ISP fs args). }
    destruct id as [|id].
    { exact (node_refront_sound HSEGS H0T NX LIM SINV argH ISP fs args). }
    intros cs cs' E R FULL model T _ _ Hn; discriminate Hn.
  Qed.

  Theorem g0_XB_sound : ext2_stmt HSEGS H0T NX LIM g0_XB SINV argH ISP fs.
  Proof. unfold ext2_stmt, g0_XB. intros. discriminate. Qed.

  (* [comment removed for export] *)
  Variable HS : nat -> option acs.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs0, env_agree NX E E' -> HOLES h E fs0 = HOLES h E' fs0.
  Hypothesis HOLES_nil : forall h E fs0, HOLES h E fs0 [].
  Hypothesis HOLES_mod : forall h E fs0, HOLES h E fs0 = HOLES (CAP.hole_cls h) E fs0.   (* [comment removed for export] *)
  Hypothesis HS_sound : holes_stmt HSEGS H0T LIM HS SINV argH ISP HOLES fs.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound HSEGS IT.
  Variable KC : nat.
  Variable GC : bool.

  Theorem g0_check_sound : forall FUEL BFUEL p cs s,
    CAP.check HSEGS IT H0T NX LIM (g0_XN NX LIM) (g0_XE NX) g0_XB HS KC true false GC BFUEL FUEL None cs p = COk s ->
    forall E R FULL model, cs_ok HSEGS H0T LIM SINV argH ISP fs E cs R FULL model ->
      crz HSEGS (cfg_of HSEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros FUEL BFUEL p cs s Hchk E R FULL model HC.
    exact (check_sound HSEGS IT IT_ok H0T NX LIM HS (g0_XN NX LIM) (g0_XE NX) g0_XB
              h0t_segs_wx h0t_in_hull h0t_hull_ok h0t_shadow_ok h0t_zone_ok NX_spw SINV argH ISP AH AA SF SA SP
              HOLES HOLES_agree HOLES_nil HOLES_mod fs KC GC
              ob_sys ob_brk2 ob_mmap2 ob_mmapin ob_mprotect2 ob_exit ob_x ob_join ob_joinx
              g0_XN_sound g0_XE_sound g0_XB_sound HS_sound
              FUEL BFUEL None p cs s Hchk E R FULL model t_nil HC I eq_refl).
  Qed.
End G0Check.
