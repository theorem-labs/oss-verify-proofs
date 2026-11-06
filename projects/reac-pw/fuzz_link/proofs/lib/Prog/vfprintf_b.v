(* reac-pw/fuzz_link, PLAIN build: vfprintf_contract (lib/Prog/vfprintf_c.v) from the CJ walk of vfprintf on
   link's memory FILE.

   `vfprintf_of_mf` takes three statements as premises: the CJ-level walk `vfprintf_mf_stmt` (lib/Prog/mf_sink_c.v,
   at link's image N_img of lib/CJ/RL/I/IImgP.v, whose GLOBALS_TOP is 0x97000 and whose sym 0x7f000400 is VFPRINTF),
   and the two FILE bridges of lib/Prog/mf_bridge_c.v (the FILE as cells before the call, `pf_file_post` from the
   cells after it). The proof is the bridge of lib/Prog/snprintf.v for snprintf (`text_ok`, `tpc` / `ta`,
   lib/CJBridge.v), with the FILE block as the destination:
   - the leaf_fp shape from a walk over `mkR` (lib/Prog/mk_leaf_fp.v `leaf_fp_intro`);
   - the stack split at lo = sp - VFPRINTF_K (VF_DEPTH = 5552 <= 5968), the CJ walk run on [lo, sp);
   - the format, its model and its argument slots from printf_facts_c (`pargs_ok_mf`: a string is outside
     [lo, sp) and outside the FILE block, so outside every region of the sink);
   - after the call: the frame munch weakened to [sp - K, sp) and the block; the stack below lo put back with
     `stk_transport` (a byte of the FILE block is in m' because the block lies outside the image's segments). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 CJBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK1j YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require ITree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Prelim FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require G_pad G_pop_arg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Printf_model Printf_text G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require IImgP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import snprintf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem mk_leaf mk_leaf_fp memfile_c printf_facts_c vfprintf_c mf_bridge_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import mf_sink_c.
Import ListNotations.
Open Scope Z_scope.

Module PIF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Local Notation N_img := IImgP.N_img.

(* ==========================================================================
   1. Image constants at N_img
   ========================================================================== *)

Lemma c_vf : @RStep.sym N_img 0x7f000400 = VFPRINTF.
Proof. vm_compute. reflexivity. Qed.
Lemma c_gtop_i : @PIF.GLOBALS_TOP N_img = IMG_TOP.
Proof. vm_compute. reflexivity. Qed.
Lemma c_got_i : @G_pad.got_ssp N_img = GOT_GUARD.
Proof. vm_compute. reflexivity. Qed.
Lemma c_guard_i : @G_pad.ssp_guard N_img = GUARD.
Proof. vm_compute. reflexivity. Qed.

(* every loaded segment of link's image lies in [IMG_LO, IMG_TOP) *)
Lemma seg_img : forall x, find_segment rsegs x 1 <> None -> IMG_LO <= x < IMG_TOP.
Proof.
  intros x H. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|congruence].
  pose proof (YK1j.find_segment_range _ _ _ _ E) as R. pose proof (YK1j.find_segment_in _ _ _ _ E) as Hin.
  assert (B : forallb (fun s => (IMG_LO <=? Z.of_N (seg_base s)) &&
                                (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? IMG_TOP)) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B s Hin). apply andb_true_iff in B. destruct B as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

(* a writable byte outside the image is a byte of m itself *)
Lemma heap_byte : forall m x, (x < IMG_LO \/ IMG_TOP <= x) -> 0 <= x < 2 ^ 64 ->
  wview rsegs m (wa x) <> None -> exists b, m (wa x) = Some b.
Proof.
  intros m x Hx Hr W. destruct (m (wa x)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. pose proof (CJ.Lib.Mem.wview_seg rsegs m (wa x) W E) as S.
  rewrite wa_unsigned in S by lia. apply seg_img in S. lia.
Qed.

(* ==========================================================================
   2. Small bridges
   ========================================================================== *)

Lemma unsigned_wz : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (wz x) = x.
Proof. intros x Hx. unfold wz. apply lib.Lib.MState.unsigned_lit. exact Hx. Qed.

Lemma res_mkR : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  res (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
  = bv_unsigned a0.
Proof. reflexivity. Qed.

Lemma u64s_flat : forall ws, CJ.Lib.Arr.u64s ws = flat_map le8 ws.
Proof.
  induction ws as [|w ws IH]; [reflexivity|]. cbn [CJ.Lib.Arr.u64s flat_map]. rewrite IH. reflexivity.
Qed.

Lemma va_of_slots : forall m ap slots, va_slots m ap slots -> @G_pop_arg.va_area N_img m ap slots.
Proof. intros m ap slots H. unfold G_pop_arg.va_area, va_slots in *. rewrite u64s_flat. exact H. Qed.

Lemma ssp_of_guard : forall m, guard_words m -> exists g, @G_pad.ssp_cells N_img m g.
Proof.
  intros m (G & g & Q). exists g. unfold G_pad.ssp_cells. rewrite c_got_i, c_guard_i.
  split; apply rw8_of_bytes; first [exact G | exact Q | vm_compute; reflexivity].
Qed.

(* the argument slots, as printf_core's sink regions see them: FILE f (232), buffer f + 280 (1024),
   RC = lo (0 bytes), RE = 1 (0 bytes), the va slot at lo *)
Lemma str_ok_mf : forall m S lo f r s,
  pf_arg_ok m S lo f MemFile.MF_BLOCK r (APtr s) -> lo + 8 <= S ->
  @PIF.arg_ok N_img f (f + 280) 1024 lo 0 1 0 m lo S lo r (Printf_model.PA_s s).
Proof.
  intros m S lo f r s [HF [slack (BY & PAD & POS & L1 & L2)]] HS.
  exists slack. unfold Prelim.zlength. unfold MemFile.MF_BLOCK in L2.
  split; [unfold pf_bytes in BY; rewrite map_app, <- app_assoc in BY; exact BY|].
  split; [exact HF|]. split; [exact PAD|]. split; [exact POS|].
  repeat split; lia.
Qed.

Lemma pargs_ok_mf : forall m S lo f ps args rs,
  pf_args_ok m S lo f MemFile.MF_BLOCK rs args -> lo + 8 <= S ->
  @PIF.args_ok N_img f (f + 280) 1024 lo 0 1 0 m lo S lo rs
    (Printf_text.pf_pargs (map tpc ps) (map ta args)).
Proof.
  intros m S lo f ps. induction ps as [|p ps IH]; intros args rs H HS; [destruct rs; exact I|].
  destruct p; cbn [map tpc Printf_text.pf_pargs].
  - apply IH; assumption.
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [exact H1 | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [exact H1 | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [split; [apply Z.mod_pos_bound; lia | exact (proj2 H1)] | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [split; [apply Z.mod_pos_bound; lia | exact (proj2 H1)] | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [exact H1 | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [exact (str_ok_mf m S lo f r s H1 HS) | apply IH; assumption].
  - destruct args as [|[k|u|s] [|[v|u2|s2] a']]; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r1 [|r2 rs]]; [destruct H | destruct H as [_ []] |]. destruct H as [H1 [H2 H3]].
    split; [exact H1|]. split; [exact (str_ok_mf m S lo f r2 s2 H2 HS) | apply IH; assumption].
Qed.

(* the stack below lo after the call: the FILE block is the only part of the call's writes below lo, and each
   of its bytes is a byte of m' (it lies outside the image) *)
Lemma stk_back : forall m m' lo0 lo hi f,
  stk rsegs m lo0 lo ->
  munch [(lo, hi); (f, f + 232); (f + 280, f + 1304)] m m' -> wmono rsegs m m' ->
  wr_at rsegs m f MemFile.MF_BLOCK -> mf_place_ok f -> stk rsegs m' lo0 lo.
Proof.
  intros m m' lo0 lo hi f ST MU WM WR PL.
  pose proof ST as (S0 & S1 & _).
  apply (stk_transport rsegs _ m m' lo0 lo ST MU WM).
  intros x Hx.
  destruct (Z_lt_le_dec x f) as [H1|H1]; [left; cbn [outside]; repeat split; lia|].
  destruct (Z_lt_le_dec x (f + 1304)) as [H2|H2]; [right | left; cbn [outside]; repeat split; lia].
  destruct WR as (W0 & W1 & W). unfold MemFile.MF_BLOCK in *.
  apply heap_byte; [unfold mf_place_ok, MemFile.MF_BLOCK in PL; lia | lia |].
  apply WM. replace x with (f + (x - f)) by lia. apply W. lia.
Qed.

(* ==========================================================================
   3. vfprintf_contract
   ========================================================================== *)

Theorem vfprintf_of_mf : mf_cells_of_k_stmt -> mf_post_of_cells_stmt -> @vfprintf_mf_stmt N_img -> vfprintf_contract.
Proof.
  intros CELLS POST VF0. unfold vfprintf_contract.
  intros f k fl om wend wpos wbase pos len pb fmt ps args T slots.
  apply leaf_fp_intro.
  - intros r1 r2 m0 H P. unfold getr_same in H. cbv beta in P |- *. unfold arg, spZ in P |- *.
    rewrite !H in P. exact P.
  - intros r1 r2 m0 H. reflexivity.
  - intros r1 r2 m0 q1 q2 m' H1 H2 P. unfold getr_same in H2. cbv beta in P |- *. unfold res in P |- *.
    rewrite !H2 in P. exact P.
  - unfold leaf_fp_walk.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo0.
    cbv beta zeta.
    intros PRE MI TM ST LO SP FR IT GG GQ.
    rewrite mkR_a0, mkR_a1, mkR_a2, mkR_sp in PRE.
    destruct PRE as (A0 & MK & DYN & PBY & LPB & BYF & RLO & REND & PARSE & TEXT & VAS & SPA & VAHI & PAOK & FIT
                     & FLO & ILO & GW).
    pose proof (memfile_k_at m f k MK) as (F0 & _).
    pose proof (memfile_k_place m f k MK) as PL.
    pose proof (memfile_k_range m f k MK) as KR.
    pose proof MK as (_ & _ & WRB & _).
    destruct (CELLS m f k fl om wend wpos wbase pos len pb MK DYN PBY LPB)
      as (jp & jc & j48 & j64 & j104 & jx & bjunk & RWF & RWB & LEN & WIN & FL8 & OM).
    pose proof DYN as (DF & DO & DE & DP & DB & _).
    destruct (ssp_of_guard m GW) as [cn SSP].
    destruct (text_ok _ _ _ _ _ _ fmt ps args T PAOK PARSE TEXT
                ltac:(unfold MemFile.MF_BUFSIZ in FIT; lia)) as (MODEL & P1 & HF).
    assert (Elo : exists lo, lo = bv_unsigned sp - VFPRINTF_K) by (eexists; reflexivity).
    destruct Elo as [lo Elo].
    rewrite <- Elo in PAOK, FLO, ILO.
    destruct (stk_split rsegs m lo0 lo (bv_unsigned sp) ST ltac:(unfold VFPRINTF_K in *; lia)) as [ST1 ST2].
    (* the premises of the CJ walk *)
    assert (E0 : a0 = Z_to_bv 64 f) by (rewrite <- A0; exact (eq_sym (Z_to_bv_bv_unsigned a0))).
    pose proof (proj2 (rw_cells_iff rsegs m f _) RWF) as RWFc. cbn [map cell_to mf_file_l] in RWFc.
    pose proof (proj2 (rw_cells_iff rsegs m (f + MemFile.MF_BUF) [CB (length pb) pb; CB (length bjunk) bjunk]) RWB)
      as RWBc.
    cbn [map cell_to] in RWBc.
    assert (WINc : (bv_unsigned (wz wend) = 0 /\ k = 0) \/
                   (bv_unsigned (wz wend) = f + 1304 /\ bv_unsigned (wz wpos) = f + 280 + k /\
                    bv_unsigned (wz wbase) = f + 280)).
    { rewrite !unsigned_wz by lia. unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ in WIN. lia. }
    assert (FL8c : Z.land (bv_unsigned (wz fl)) 8 = 0) by (rewrite unsigned_wz by lia; exact FL8).
    assert (OMc : bv_unsigned (wz om) = 0 \/ bv_unsigned (wz om) = 4294967295)
      by (rewrite unsigned_wz by lia; unfold YI14.U32M1 in OM; exact OM).
    assert (LBF : 2147483648 <= bv_unsigned (wz YI14.U32M1) mod 4294967296)
      by (apply Z.leb_le; vm_compute; reflexivity).
    pose proof (va_of_slots m (bv_unsigned a2) slots VAS) as VAc.
    pose proof (pargs_ok_mf m (bv_unsigned sp) lo f ps args slots PAOK
                  ltac:(rewrite Elo; unfold VFPRINTF_K; lia)) as AOK.
    pose proof (mem_inv_to_cj rsegs m MI TM) as MIc.
    unfold vfprintf_mf_stmt in VF0.
    pose proof (VF0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m f k (wz fl) jp jc (wz wend) (wz wpos) j48 (wz wbase) j64 j104 (wz om) (wz YI14.U32M1) jx pb bjunk
                (bv_unsigned a1) (bv_unsigned a2) (Prelim.zlength T) (fmt ++ [0]) slots
                (Printf_text.pf_pargs (map tpc ps) (map ta args)) lo cn (Prelim.zlength T) T) as VF.
    clear VF0.
    cbv zeta in VF. rewrite c_vf, c_gtop_i in VF.
    specialize (VF E0 (eq_sym (Z_to_bv_bv_unsigned a1)) (eq_sym (Z_to_bv_bv_unsigned a2)) RWFc RWBc LPB LEN
                WINc FL8c OMc LBF BYF HF P1 VAc AOK MODEL
                ltac:(unfold Prelim.zlength; lia)
                ltac:(unfold Prelim.zlength, MemFile.MF_BUFSIZ in *; lia)
                ST2 ltac:(unfold PIF.VF_DEPTH, VFPRINTF_K in *; lia) ILO SP SSP MIc FR
                ltac:(unfold Prelim.zlength, PIF.STATIC_SPLIT, RO_END in *; rewrite length_app; cbn [length]; lia)
                ltac:(unfold RO_LO in RLO; lia)
                SPA ltac:(unfold Prelim.zlength; lia) F0 FLO
                ltac:(unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK in *; lia)).
    (* the post *)
    eapply evt_bridge; [|exact VF].
    intros ms' P. unfold vfprintf_mf_post in P.
    destruct P as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & bj
                   & m' & Hms & MU & WM & MI' & FRM & FOK & ST' & _ & RWF' & RWB' & RR).
    destruct (mem_inv_of_cj rsegs m' MI') as [MI2 TM2].
    pose proof (proj1 (munch_iff _ _ _) MU) as MUl. clear MU. rename MUl into MU.
    pose proof (proj1 (wmono_iff _ _ _) WM) as WMl. clear WM. rename WMl into WM.
    pose proof (proj1 (stk_iff _ _ _ _) ST') as STl. clear ST'. rename STl into ST'.
    exists (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Prelim.zlength T)) a1' a2' a3' a4' a5' a6' a7'
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'), Ft, fc', m'.
    split; [exact Hms|]. split; [exact FRM|]. split; [exact FOK|].
    split; [apply regs_preserved_mkR|].
    split.
    { eapply munch_weaken; [|exact MU]. intros x Hx. unfold mf_block in Hx. cbn [outside fst snd] in Hx |- *.
      destruct Hx as (H1 & H2 & _). unfold MemFile.MF_BLOCK in H2. repeat split; lia. }
    split; [exact WM|]. split; [exact MI2|]. split; [exact TM2|].
    split.
    { apply (stk_merge rsegs m' lo0 lo (bv_unsigned sp)); [| exact ST' | unfold VFPRINTF_K in *; lia].
      exact (stk_back m m' lo0 lo (bv_unsigned sp) f ST1 MU WM WRB PL). }
    split.
    { rewrite res_mkR. rewrite lib.Lib.MState.unsigned_lit by (unfold CJ.Spec.FmtFp.INT_MAX in RR; lia). reflexivity. }
    apply (POST m m' f k fl om wend wpos wbase pos len lo (bv_unsigned sp) pb T jp jc j48 j64 j104 jx bj
             MK DYN LPB RWF MU FLO ltac:(unfold MemFile.MF_BLOCK, VFPRINTF_K in *; lia) WM).
    + rewrite unsigned_wz in RWF' by lia.
      replace (f + MemFile.MF_BUF + MemFile.MF_BUFSIZ) with (f + 1304)
        by (unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ; lia).
      apply (proj1 (rw_cells_iff rsegs m' f _)). cbn [map cell_to mf_file_l].
      unfold mf_file in RWF'. revert RWF'. destruct (wend =? 0); intros RWF'; exact RWF'.
    + apply (proj1 (rw_cells_iff rsegs m' (f + MemFile.MF_BUF) _)). cbn [map cell_to]. exact RWB'.
    + exact FIT.
Qed.
