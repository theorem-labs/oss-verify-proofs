(* SCRATCH (a Theorem Labs lane): the resume after one of put_string's put calls, image A (fs.asan), folded by
   a Theorem Labs lane into FSW_put_string.v. FSW_put_string.ps_put_call hands its continuation the ONE-region resume
   `fss_ret_s0 r (-104) 0 ps_sv_chunks` (the caller's saved words at s0, atom 8) over the env of ps_epilogue
   (fs_extraT ++ ps_xs regs0 FL ++ [shadow_addr F]); the joins of ZZpsjoin.v start from the FULL return shape
   FSW_put_string.ps_ret_ss. psr_resume is the bridge, psr_resume_epi its instance at put #3's return (the state
   ps_epilogue takes).
   How (no bridge, no realizes): the three registers named by a region are re-seated (YI08.st_ok_set_reg), and the
   memory and facts of the state are replaced whole (psr_st_ok_reseat). The five fixed regions are proved here:
   - atom 8, the saved words: the resume's own region, unchanged;
   - atom 9, the re-aligned frame [sp1, sp1 + 88): writable because the journal's window [jt - STK, jt) is present
     (YCbq.ajournal, 14th clause) and lies in high memory, so `unpoison` keeps it (FSW_K.fsw_apresent_unpoison);
   - atom 24, the fake frame, and atom 47, its eight shadow bytes: present and not owned at the post state
     (AR_frames_law), so present on the machine's memory (FSW_frame.fsw_apresent_notowned);
   - xatom 13, the flag byte: present at the post state (AR_flag_law) and in application memory, so `unpoison`
     does not change it (psr_app_apresent, the proof of FSW_put_string.ps_app_unpoison on apresent);
   their pairwise disjointness from the stack bound (astk_ok: the window is above alloc_ceiling), YCbq.frames_bounds
   (the frame below it), ps_frame_sh_disj, and the flag byte being owned while every frame and shadow byte is not.
   The slot chunks, the frame header and shadow chunks, and the extra regions rs (with their disjointness) are the
   caller's premises. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YCeo.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame
FSW_frame3 FSW_writer_tbl FSW_writer_model FSW_put_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer FSW_writer_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the six atom facts of the return shape that do not name the string: ps_ret_atoms L without its last entry (atom
   26), in ps_ret_atoms' order; it is exactly the fact list of ps_epi_ss *)
Definition psr_atoms6 : list (nat * afact) :=
  [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 88) 5);
   (24%nat, mkAF 4096 (2 ^ 47 - 64) 5); (47%nat, mkAF 0 (2 ^ 47) 0);
   (xatom 13, mkAF 4096 (2 ^ 47 - 1) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].

(* ---- small list, fact and arithmetic lemmas (never in a walk's context) ---- *)
(* re-seat a state on a new env / register file: the TEXT of ZZpsjoin.v's psj_st_ok_reseat (a Theorem Labs lane), renamed *)
Lemma psr_st_ok_reseat : forall {fx : YK11.FPState} E E' ss ss' ms,
  st_ok tfibsegs E ss ms -> ss_resv ss = None -> ss_pc ss' = ss_pc ss -> ss_resv ss' = None ->
  YP0l.regs_ok E' (ss_regs ss') (ms_regs ms) -> mem_ok tfibsegs E' (ms_mem ms) (ss_mem ss') ->
  facts_ok E' (ss_facts ss') -> st_ok tfibsegs E' ss' ms.
Proof.
  intros fx E E' ss ss' ms (H1 & H2 & H3 & H4 & H5 & H6 & _ & _ & _) Hr Hpc Hr' HR HM HF.
  rewrite Hr in H4. unfold st_ok. rewrite Hpc, Hr'.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6|]. split; [exact HR|]. split; [exact HM | exact HF].
Qed.

Lemma psr_ad_app : forall E r l rs,
  YP09.all_disjoint E r l -> YP09.all_disjoint E r rs -> YP09.all_disjoint E r (l ++ rs).
Proof.
  intros E r l rs. induction l as [|r' l IH]; cbn [YP09.all_disjoint app].
  - intros _ H. exact H.
  - intros (H1 & H2) H3. exact (conj H1 (IH H2 H3)).
Qed.

Lemma psr_pd_app : forall E l rs,
  YP09.pairwise_disjoint E l -> Forall (fun r0 => YP09.all_disjoint E r0 rs) l ->
  YP09.pairwise_disjoint E rs -> YP09.pairwise_disjoint E (l ++ rs).
Proof.
  intros E l rs. induction l as [|r l IH]; cbn [YP09.pairwise_disjoint app].
  - intros _ _ H. exact H.
  - intros (H1 & H2) HF H3.
    exact (conj (psr_ad_app E r l rs H1 (Forall_inv HF)) (IH H2 (Forall_inv_tail HF) H3)).
Qed.

Lemma psr_afact : forall E n v lo hi al,
  bv_unsigned (ew E n) = v -> lo <= v <= hi -> v mod 2 ^ al = 0 -> ((0 <=? al) && (al <=? 64)) = true ->
  afact_ok E n (mkAF lo hi al).
Proof.
  intros E n v lo hi al Hv H1 H2 H3. apply andb_prop in H3 as [H3a H3b].
  apply Z.leb_le in H3a, H3b. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hv.
  exact (conj H1 (conj H2 (conj H3a H3b))).
Qed.

(* a point outside an interval lies wholly on one side of it *)
Lemma psr_pt_out : forall a lo n, (lo <= a < lo + n -> False) -> a + 1 <= lo \/ lo + n <= a.
Proof.
  intros a lo n H. destruct (Z.ltb_spec a lo) as [H1 | H1]; [left; lia|].
  destruct (Z.ltb_spec a (lo + n)) as [H2 | H2]; [exfalso; apply H; lia | right; lia].
Qed.

(* the five fixed extents of the return shape are pairwise apart *)
Lemma psr_disj5 : forall sp0 sp1 F shF FL ac,
  sp1 + 192 <= sp0 -> ac <= sp1 -> F + 64 <= ac -> shF + 8 <= ac -> FL + 1 <= ac ->
  (shF + 8 <= F \/ F + 64 <= shF) -> (FL + 1 <= F \/ F + 64 <= FL) -> (FL + 1 <= shF \/ shF + 8 <= FL) ->
  zpairwise_disjoint [(sp0 + -104, sp0 + 0); (sp1 + 0, sp1 + 88); (F + 0, F + 64); (shF + 0, shF + 8);
                      (FL + 0, FL + 1)].
Proof.
  intros sp0 sp1 F shF FL ac H1 H2 H3 H4 H5 H6 H7 H8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the frame's shadow lies below alloc_ceiling (and so below the stack) *)
Lemma psr_sh_bd : forall F, 4096 <= F -> F + 64 <= alloc_ceiling ->
  0 <= shadow_addr F /\ shadow_addr F + 8 <= alloc_ceiling.
Proof.
  intros F H1 H2. pose proof asan_consts as (C1 & _). unfold shadow_addr, SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* a present byte of application memory is present on the machine's memory: `unpoison` only rewrites shadow bytes
   of the user-poisoned heads (FSupoison.ush_facts), never an application byte. The proof of
   FSW_put_string.ps_app_unpoison, stated on apresent. *)
Lemma psr_app_apresent : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> in_app a 1 ->
  apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) mem a.
Proof.
  intros ly S U W mem md a HARU Ha Happ (Hh & b & Hb). split; [exact Hh|]. exists b.
  rewrite <- Hb. symmetry. apply unpoison_out. rewrite (wz a Ha).
  destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
  destruct (ush_facts tfibsegs B ly S U W mem md a HARU E) as (_ & L1 & L2).
  unfold in_app, kLowShadowBeg, SHADOW_OFF, ASAN_CEIL, kHighMemBeg in *. lia.
Qed.

(* ================= the resume, with the facts beyond the six fixed ones left open ================= *)
Lemma psr_resume_core : forall STK jt sp0 FP ly S W0 mem0 md0 own ly' S' U' (W' : world tfibsegs) mem' md' k
    regs' regs0 r pos F FL sp1 scs rs A,
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
    (fss_ret_s0 r (-104) 0 ps_sv_chunks)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK jt FP ly S W0 mem0 md0 own ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly' S' U' W' mem' md' ->
  In (0, pos) (frames S') -> F = frame_addr ly' 0 pos -> FL = flag_addr ly' 0 pos ->
  YK11.getr regs' 8%bv = Z_to_bv 64 sp0 -> YK11.getr regs' 9%bv = Z_to_bv 64 sp1 ->
  YK11.getr regs' 21%bv = Z_to_bv 64 F -> YK11.getr regs' 22%bv = Z_to_bv 64 (shadow_addr F) ->
  YK11.getr regs' 23%bv = Z_to_bv 64 SHADOW_OFF -> YK11.getr regs' 24%bv = Z_to_bv 64 F ->
  jt - STK <= sp1 -> sp1 + 192 <= sp0 -> sp0 <= jt -> sp1 mod 32 = 0 ->
  YP09.region_wf (YP09.mkRegion (Some 9%nat) 0 88 0 88 scs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
            (mrestrict (w_H W') mem') sp1) scs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
            (mrestrict (w_H W') mem') F) ps_hdr_chunks ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
            (mrestrict (w_H W') mem') (shadow_addr F)) ps_fsh_chunks ->
  YP09.regions_wf rs = true ->
  Forall (YP09.region_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
            (mrestrict (w_H W') mem')) rs ->
  Forall (fun r0 => YP09.all_disjoint (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
                      r0 rs) (ps_ret_regions scs []) ->
  YP09.pairwise_disjoint (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)])) rs ->
  atoms_ok (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)])) A ->
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
    (mkSS r ps_ret_regs (ps_ret_regions scs rs) None (mkFacts (psr_atoms6 ++ A) [] []))
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros STK jt sp0 FP ly S W0 mem0 md0 own ly' S' U' W' mem' md' k regs' regs0 r pos F FL sp1 scs rs A
  HS HJ HARU Hin EF EFL E8 E9 E21 E22 E23 E24 Hwin Hsp1 Hjt Hal1 Hwf9 Hscs Hhdr Hfsh Hwfrs Hokrs Hdjrs Hpdrs HA.
subst F FL.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly' S' U' W' mem' md' HARU) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (al_frames _ _ LAWS ly' S' W' (unpoison U' mem') md' 0 pos HAR Hin) as (Hal32 & _ & Hfp & Hshp).
destruct (frames_bounds tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' 0 pos HAR Hin) as (H4096 & Hfc & Hfapp).
destruct (al_flag _ _ LAWS ly' S' W' (unpoison U' mem') md' 0 pos HAR Hin) as (Hflp & Hflo & Hflapp & Hflc).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
rewrite Hfb in Hfp, Hshp, Hfc, Hfapp. change (64 / 8) with 8 in Hshp.
set (F := frame_addr ly' 0 pos) in *. set (FL := flag_addr ly' 0 pos) in *.
set (X := fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]) in *.
(* ---- the arithmetic, each fact in a small context ---- *)
assert (Bsp : alloc_ceiling <= sp1 /\ sp1 + 192 <= sp0 /\ sp0 <= 2 ^ 47)
  by (clear - Hceil Hslo Hwin Hsp1 Hjt Hshi H47; lia).
assert (Fb : 4096 <= F /\ F + 64 <= alloc_ceiling) by (clear - H4096 Hfc; lia).
pose proof (psr_sh_bd F (proj1 Fb) (proj2 Fb)) as Shb.
assert (FLb : 4096 <= FL /\ FL + 1 <= alloc_ceiling)
  by (clear - Hflapp Hflc; unfold in_app in Hflapp; lia).
assert (B9 : 2 ^ 46 <= sp1 <= 2 ^ 47 - 88) by (clear - Bsp C1; lia).
assert (B24 : 4096 <= F <= 2 ^ 47 - 64) by (clear - Fb C1; lia).
assert (B47 : 0 <= shadow_addr F <= 2 ^ 47) by (clear - Shb C1; lia).
assert (B46 : 4096 <= FL <= 2 ^ 47 - 1) by (clear - FLb C1; lia).
(* ---- the env's atoms ---- *)
assert (U8 : bv_unsigned (ew (Ereg regs' X) 8) = sp0)
  by (rewrite (ew_Ereg_nat regs' X 8 8%bv eq_refl), E8; apply wz; clear - Bsp C1; lia).
assert (U9 : bv_unsigned (ew (Ereg regs' X) 9) = sp1)
  by (rewrite (ew_Ereg_nat regs' X 9 9%bv eq_refl), E9; apply wz; clear - Bsp C1; lia).
assert (U24 : bv_unsigned (ew (Ereg regs' X) 24) = F)
  by (rewrite (ew_Ereg_nat regs' X 24 24%bv eq_refl), E24; apply wz; clear - B24; lia).
assert (U32 : ew (Ereg regs' X) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32u : bv_unsigned (ew (Ereg regs' X) 32) = SHADOW_OFF)
  by (rewrite U32; apply wz; unfold SHADOW_OFF; lia).
assert (U46 : bv_unsigned (ew (Ereg regs' X) (xatom 13)) = FL)
  by (unfold X, xatom; change (33 + 13)%nat with (32 + 14)%nat; rewrite ew_Ereg_extra;
      cbn [nth fs_extraT ps_xs app]; apply wz; clear - B46; lia).
assert (U47e : ew (Ereg regs' X) 47 = Z_to_bv 64 (shadow_addr F))
  by (unfold X; change 47%nat with (32 + 15)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U47 : bv_unsigned (ew (Ereg regs' X) 47) = shadow_addr F)
  by (rewrite U47e; apply wz; clear - B47; lia).
(* ---- the register re-seat: s7 = the shadow base, s5 = the frame, s6 = the frame's shadow ---- *)
assert (R23 : YK11.getr regs' 23%bv = sv_denot (Ereg regs' X) (SOff 32 0)) by (rewrite fsw_SOff0, U32; exact E23).
assert (R21 : YK11.getr regs' 21%bv = sv_denot (Ereg regs' X) (SOff 24 0)).
{ rewrite fsw_SOff0, (ew_Ereg_nat regs' X 24 24%bv eq_refl), E24. exact E21. }
assert (R22 : YK11.getr regs' 22%bv = sv_denot (Ereg regs' X) (SOff 47 0)) by (rewrite fsw_SOff0, U47e; exact E22).
pose proof (st_ok_set_reg tfibsegs (Ereg regs' X) _ _ 23%bv (SOff 32 0) HS ltac:(discriminate) R23) as HS1.
pose proof (st_ok_set_reg tfibsegs (Ereg regs' X) _ _ 21%bv (SOff 24 0) HS1 ltac:(discriminate) R21) as HS2.
pose proof (st_ok_set_reg tfibsegs (Ereg regs' X) _ _ 22%bv (SOff 47 0) HS2 ltac:(discriminate) R22) as HS3.
clear HS1 HS2.
(* ---- what the resume already holds: the saved-words region and its atom fact ---- *)
assert (R8ok : YP09.region_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W') mem')
                 (YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 ps_sv_chunks))
  by (destruct (st_ok_mem_ok tfibsegs (Ereg regs' X) _ _ HS) as (_ & HF8 & _); exact (Forall_inv HF8)).
assert (A8 : afact_ok (Ereg regs' X) 8 (mkAF (2 ^ 46) (2 ^ 47) 4))
  by exact (proj1 (proj1 (st_ok_facts_ok tfibsegs (Ereg regs' X) _ _ HS))).
(* ---- the four other fixed regions ---- *)
assert (R9ok : YP09.region_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W') mem')
                 (YP09.mkRegion (Some 9%nat) 0 88 0 88 scs)).
{ unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [clear - Bsp C1; lia|]. split; [clear - Bsp; lia|]. split; [|exact Hscs].
  intros o Ho. apply (apresent_writable tfibsegs).
  apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU); [clear - Bsp C1 C3 Ho; lia|].
  apply Hpres. clear - Hwin Hsp1 Hjt Ho; lia. }
assert (R24ok : YP09.region_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W') mem')
                  (YP09.mkRegion (Some 24%nat) 0 64 0 64 ps_hdr_chunks)).
{ unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U24. split; [clear - B24; lia|]. split; [clear - B24; lia|]. split; [|exact Hhdr].
  intros o Ho. apply (apresent_writable tfibsegs).
  destruct (Hfp (F + o) ltac:(clear - Ho; lia)) as (Hp & Hno).
  exact (fsw_apresent_notowned B ly' S' U' W' mem' md' (F + o) HARU ltac:(clear - B24 Ho; lia) Hno Hp). }
assert (R47ok : YP09.region_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W') mem')
                  (YP09.mkRegion (Some 47%nat) 0 8 0 8 ps_fsh_chunks)).
{ unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U47. split; [clear - B47; lia|]. split; [clear - B47; lia|]. split; [|exact Hfsh].
  intros o Ho. apply (apresent_writable tfibsegs).
  destruct (Hshp o Ho) as (Hp & Hno).
  exact (fsw_apresent_notowned B ly' S' U' W' mem' md' (shadow_addr F + o) HARU
           ltac:(clear - B47 Ho; lia) Hno Hp). }
assert (RFLok : YP09.region_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W') mem')
                  (YP09.mkRegion (Some (xatom 13)) 0 1 0 1 [])).
{ unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U46. split; [clear - B46; lia|]. split; [clear - B46; lia|]. split; [|apply Forall_nil].
  intros o Ho. assert (o = 0) as -> by (clear - Ho; lia). rewrite Z.add_0_r.
  apply (apresent_writable tfibsegs).
  exact (psr_app_apresent ly' S' U' W' mem' md' FL HARU ltac:(clear - B46; lia) Hflapp Hflp). }
(* ---- the memory: well-formed, every region ok, pairwise apart ---- *)
assert (WF : YP09.regions_wf (ps_ret_regions scs rs) = true).
{ unfold ps_ret_regions. cbn [YP09.regions_wf]. rewrite Hwf9, Hwfrs. vm_compute. reflexivity. }
assert (OK : Forall (YP09.region_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W') mem')) (ps_ret_regions scs rs)).
{ unfold ps_ret_regions.
  constructor; [exact R8ok|]. constructor; [exact R9ok|]. constructor; [exact R24ok|].
  constructor; [exact R47ok|]. constructor; [exact RFLok | exact Hokrs]. }
pose proof (ps_frame_sh_disj F Hfapp) as HFS.
assert (HFF : FL + 1 <= F \/ F + 64 <= FL)
  by (apply psr_pt_out; intros Hr; exact (proj2 (Hfp FL Hr) Hflo)).
assert (HSF : FL + 1 <= shadow_addr F \/ shadow_addr F + 8 <= FL).
{ apply psr_pt_out. intros Hr.
  destruct (Hshp (FL - shadow_addr F) ltac:(clear - Hr; lia)) as (_ & Hno).
  replace (shadow_addr F + (FL - shadow_addr F)) with FL in Hno by ring. exact (Hno Hflo). }
assert (PD : YP09.pairwise_disjoint (Ereg regs' X) (ps_ret_regions scs rs)).
{ change (ps_ret_regions scs rs) with (ps_ret_regions scs [] ++ rs).
  apply psr_pd_app; [|exact Hdjrs|exact Hpdrs].
  apply pairwise_disjoint_of_extents. unfold ps_ret_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U9, U24, U47, U46.
  exact (psr_disj5 sp0 sp1 F (shadow_addr F) FL alloc_ceiling (proj1 (proj2 Bsp)) (proj1 Bsp) (proj2 Fb)
           (proj2 Shb) (proj2 FLb) HFS HFF HSF). }
(* ---- the facts ---- *)
assert (HF : facts_ok (Ereg regs' X) (mkFacts (psr_atoms6 ++ A) [] [])).
{ split; [|split; exact I]. cbn [f_atoms]. unfold psr_atoms6. cbn [app atoms_ok].
  refine (conj A8 (conj _ (conj _ (conj _ (conj _ (conj _ HA)))))).
  - exact (psr_afact _ 9 sp1 _ _ 5 U9 B9 Hal1 eq_refl).
  - exact (psr_afact _ 24 F _ _ 5 U24 B24 Hal32 eq_refl).
  - exact (psr_afact _ 47 (shadow_addr F) _ _ 0 U47 B47 (Z.mod_1_r _) eq_refl).
  - exact (psr_afact _ (xatom 13) FL _ _ 0 U46 B46 (Z.mod_1_r _) eq_refl).
  - exact (psr_afact _ 32 SHADOW_OFF _ _ 0 U32u (conj (Z.le_refl _) (Z.le_refl _)) (Z.mod_1_r _) eq_refl). }
(* ---- the new state ---- *)
apply (psr_st_ok_reseat (Ereg regs' X) (Ereg regs' X) _ _ _ HS3).
- reflexivity.
- reflexivity.
- reflexivity.
- exact (st_ok_regs_ok tfibsegs (Ereg regs' X) _ _ HS3).
- exact (conj WF (conj OK PD)).
- exact HF.
Qed.

(* ================= the resume after any of the three put calls ================= *)
Lemma psr_resume : forall STK jt sp0 FP ly S W0 mem0 md0 own ly' S' U' (W' : world tfibsegs) mem' md' k
    regs' regs0 r L pos F FL sp1 s scs rs,
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
    (fss_ret_s0 r (-104) 0 ps_sv_chunks)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK jt FP ly S W0 mem0 md0 own ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly' S' U' W' mem' md' ->
  In (0, pos) (frames S') -> F = frame_addr ly' 0 pos -> FL = flag_addr ly' 0 pos ->
  YK11.getr regs' 8%bv = Z_to_bv 64 sp0 -> YK11.getr regs' 9%bv = Z_to_bv 64 sp1 ->
  YK11.getr regs' 21%bv = Z_to_bv 64 F -> YK11.getr regs' 22%bv = Z_to_bv 64 (shadow_addr F) ->
  YK11.getr regs' 23%bv = Z_to_bv 64 SHADOW_OFF -> YK11.getr regs' 24%bv = Z_to_bv 64 F ->
  YK11.getr regs' 26%bv = Z_to_bv 64 s ->
  jt - STK <= sp1 -> sp1 + 192 <= sp0 -> sp0 <= jt -> sp1 mod 32 = 0 ->
  0 <= L -> 4096 <= s <= 2 ^ 47 - (L + 1) ->
  YP09.region_wf (YP09.mkRegion (Some 9%nat) 0 88 0 88 scs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
            (mrestrict (w_H W') mem') sp1) scs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
            (mrestrict (w_H W') mem') F) ps_hdr_chunks ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
            (mrestrict (w_H W') mem') (shadow_addr F)) ps_fsh_chunks ->
  YP09.regions_wf rs = true ->
  Forall (YP09.region_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
            (mrestrict (w_H W') mem')) rs ->
  Forall (fun r0 => YP09.all_disjoint (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
                      r0 rs) (ps_ret_regions scs []) ->
  YP09.pairwise_disjoint (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)])) rs ->
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]))
    (ps_ret_ss r L scs rs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros STK jt sp0 FP ly S W0 mem0 md0 own ly' S' U' W' mem' md' k regs' regs0 r L pos F FL sp1 s scs rs
  HS HJ HARU Hin EF EFL E8 E9 E21 E22 E23 E24 E26 Hwin Hsp1 Hjt Hal1 HL Hs Hwf9 Hscs Hhdr Hfsh Hwfrs Hokrs
  Hdjrs Hpdrs.
set (X := fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)]) in *.
assert (U26 : bv_unsigned (ew (Ereg regs' X) 26) = s)
  by (rewrite (ew_Ereg_nat regs' X 26 26%bv eq_refl), E26; apply wz; clear - HL Hs; lia).
exact (psr_resume_core STK jt sp0 FP ly S W0 mem0 md0 own ly' S' U' W' mem' md' k regs' regs0 r pos F FL sp1 scs rs
  [(26%nat, mkAF 4096 (2 ^ 47 - (L + 1)) 0)]
  HS HJ HARU Hin EF EFL E8 E9 E21 E22 E23 E24 Hwin Hsp1 Hjt Hal1 Hwf9 Hscs Hhdr Hfsh Hwfrs Hokrs Hdjrs Hpdrs
  (conj (psr_afact _ 26 s _ _ 0 U26 Hs (Z.mod_1_r _) eq_refl) I)).
Qed.

(* ================= at put #3's return: the state ps_epilogue takes, in ps_epilogue's env ================= *)
(* ps_ret_ss PS_CLOSE_RET L [the frame slot at +80] [] is ps_epi_ss PS_CLOSE_RET plus the string's atom fact
   (ZZpsjoin.v's psj_put3_close drops it); here psr_resume_core is taken with no fact beyond the six, which IS
   ps_epi_ss, so no string bound is asked. *)
Lemma psr_resume_epi : forall STK jt sp0 FP ly S W0 mem0 md0 own ly' S' U' (W' : world tfibsegs) mem' md' k
    regs' regs0 pos sp1,
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 (flag_addr ly' 0 pos)
                               ++ [Z_to_bv 64 (shadow_addr (frame_addr ly' 0 pos))]))
    (fss_ret_s0 PS_CLOSE_RET (-104) 0 ps_sv_chunks)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 PS_CLOSE_RET) mem' (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK jt FP ly S W0 mem0 md0 own ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly' S' U' W' mem' md' ->
  In (0, pos) (frames S') ->
  YK11.getr regs' 8%bv = Z_to_bv 64 sp0 -> YK11.getr regs' 9%bv = Z_to_bv 64 sp1 ->
  YK11.getr regs' 21%bv = Z_to_bv 64 (frame_addr ly' 0 pos) ->
  YK11.getr regs' 22%bv = Z_to_bv 64 (shadow_addr (frame_addr ly' 0 pos)) ->
  YK11.getr regs' 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs' 24%bv = Z_to_bv 64 (frame_addr ly' 0 pos) ->
  jt - STK <= sp1 -> sp1 + 192 <= sp0 -> sp0 <= jt -> sp1 mod 32 = 0 ->
  YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 (flag_addr ly' 0 pos)
                                       ++ [Z_to_bv 64 (shadow_addr (frame_addr ly' 0 pos))]))
    (mrestrict (w_H W') mem') sp1 (YP09.mkChunk 80 (CVal 8 (SOff 24 0))) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 (flag_addr ly' 0 pos)
                                               ++ [Z_to_bv 64 (shadow_addr (frame_addr ly' 0 pos))]))
            (mrestrict (w_H W') mem') (frame_addr ly' 0 pos)) ps_hdr_chunks ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 (flag_addr ly' 0 pos)
                                               ++ [Z_to_bv 64 (shadow_addr (frame_addr ly' 0 pos))]))
            (mrestrict (w_H W') mem') (shadow_addr (frame_addr ly' 0 pos))) ps_fsh_chunks ->
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs0 (flag_addr ly' 0 pos)
                               ++ [Z_to_bv 64 (shadow_addr (frame_addr ly' 0 pos))]))
    (ps_epi_ss PS_CLOSE_RET)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 PS_CLOSE_RET) mem' (seg_rom tfibsegs))).
Proof.
intros STK jt sp0 FP ly S W0 mem0 md0 own ly' S' U' W' mem' md' k regs' regs0 pos sp1
  HS HJ HARU Hin E8 E9 E21 E22 E23 E24 Hwin Hsp1 Hjt Hal1 H80 Hhdr Hfsh.
exact (psr_resume_core STK jt sp0 FP ly S W0 mem0 md0 own ly' S' U' W' mem' md' k regs' regs0 PS_CLOSE_RET pos
  (frame_addr ly' 0 pos) (flag_addr ly' 0 pos) sp1 [YP09.mkChunk 80 (CVal 8 (SOff 24 0))] [] []
  HS HJ HARU Hin eq_refl eq_refl E8 E9 E21 E22 E23 E24 Hwin Hsp1 Hjt Hal1
  ltac:(vm_compute; reflexivity) ltac:(constructor; [exact H80 | constructor]) Hhdr Hfsh eq_refl ltac:(constructor)
  ltac:(apply Forall_forall; intros r0 _; exact I) I I).
Qed.

End R.
