From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger ManifestB names_c as_ruled_c KindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import printf_facts_c snprintf_c plain_c strlen_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import crt_lib crt_inv crt_aux crt_text crt_ka0 crt_snp crt_whole crt_ka1 crt_ka2 crt_ka3.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import AgCf names_c_cf as_ruled_c_cf check_round_trip_c_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import crt_glue.
Import ListNotations.
Local Open Scope Z_scope.

(* Cut-free (agreement) twins of the SR-form lemmas of crt_glue.v (check_round_trip, plain): SRcf in place of SR,
   the cut-free contracts of names, as_ruled, malloc and free (NCF, ACF, MCF, FCF), the agreement room at the malloc
   site (AgCf.room_ag_of, room_cf_of_limit under LIMLAW), and the agreement cap and byte bounds (sb_cap b <= CAP_AG, bytes
   after the call <= 2^29). The pure definitions and lemmas of crt_glue.v are reused through the local notations
   below (each one is the crt_glue constant applied to this section's variables). *)

Lemma ka_step_cf : forall {fx1 : FPState} (B : malloc_syms) (P : machine_state -> Prop) regs1 pc mem1 md1 Q',
  ms_segs B = rsegs -> ro_agree rsegs mem1 -> m_halted md1 = None -> m_vm_lazy md1 = [] ->
  evt rsegs P (MS (mkR_of regs1) (@fp_regs fx1) pc (@fp_csr fx1) None (normalize_cj rsegs mem1) (seg_rom rsegs)) ->
  (forall s s0, P s0 -> ms_rel_cj rsegs s s0 -> cj_same rsegs mem1 (ms_mem s) -> forall ms', ms_eqv s ms' ->
     SRcf B (mkCfg ms' md1) Q') ->
  SRcf B (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) Q'.
Proof.
  intros fx1 B P regs1 pc mem1 md1 Q' SEG RA Hh Hl EV K.
  eapply (evt_SRcf_canon_r B SEG); [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. rewrite SEG. apply (evt_normalize_cj rsegs); [exact FrameAPI.wx_apart_rsegs | exact RA | exact EV]. }
  intros ms' (s & (s0 & HP & HR & HO) & EQ). exact (K s s0 HP HR HO ms' EQ).
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis NCF : forall fx', @names_contract_cf fx' rc B API.
Hypothesis ACF : forall fx', @as_ruled_contract_cf fx' rc B API.
Hypothesis MCF : forall fx', @malloc_contract_cf fx' rc B API.
Hypothesis FCF : forall fx', @free_contract_cf fx' rc B API.
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).
Hypothesis SFA : statics_facts B.
Hypothesis SF : statics_free B MR.
Hypothesis ERR : errno_low B.
Hypothesis CTX : ManifestB.ctx_owned B MR.
Hypothesis GS : guard_syms B.
Hypothesis SNE : statics_noerrno B.
Hypothesis MSO : malloc_syms_omx B.
Hypothesis AX : YL01.AllocExtra B MR.
Hypothesis BSP : block_slack_present B API.

Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (b : sbound) (u us : list byte) (Lam : list (Z * Z)) (peak cnt fail ua uk : Z).
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis PRE : call_pre_k B MR CRT_K L A regs mem md.
Hypothesis RA0 : ro_agree rsegs mem.
Hypothesis CU0 : cstr_at mem (bv_unsigned (getr regs 10)) u us.
Hypothesis UB : In (ua, uk) (blocks L A).
Hypothesis UL : ua <= bv_unsigned (getr regs 10).
Hypothesis UR : bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1 <= ua + uk.
Hypothesis LEN : (length u <= 255)%nat.
Hypothesis IMG : img_strings mem.
Hypothesis LG : ledger B L A mem Lam peak cnt fail.
Hypothesis QT : quiet cnt fail 1019.
Hypothesis CS0 : crt_strings mem.
Hypothesis SNP : snprintf_contract.
Hypothesis STRL : strlen_contract.
Hypothesis PLN : plain_contract.
Hypothesis CAP0 : sb_live b + 2 <= sb_cap b <= CAP_AG.
Hypothesis BY0 : 0 <= sb_bytes b.
Hypothesis BYU : sb_bytes b + (4 * Z.of_nat (length u) + 83) <= 2 ^ 29.
Hypothesis RES0 : res_ok_slots A b.
Hypothesis FRM0 : frm_zero (@fp_csr fx).
Hypothesis INIT0 : st_init_done A = true.
Hypothesis SPT : spZ regs <= TASK_SIZE.

(* The halts-form bounds the reused crt_glue lemmas take, from the agreement bounds. *)
Lemma CAP0o : sb_live b + 2 <= sb_cap b <= CAPMAX.
Proof. pose proof CAP0 as H. pose proof CAP_AG_le_CAPMAX. unfold CAPMAX in *. lia. Qed.

Lemma BYUo : sb_bytes b + (4 * Z.of_nat (length u) + 83) <= 2 ^ 40.
Proof. assert (2 ^ 29 <= 2 ^ 40) by (apply Z.pow_le_mono_r; lia). lia. Qed.

Lemma cap_nn : 0 <= sb_cap b.
Proof. destruct RES0 as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). lia. Qed.

Local Abbreviation nm_pk := (@crt_glue.nm_pk u Lam).
Local Abbreviation nm_c := (@crt_glue.nm_c u).
Local Abbreviation pre_facts := (@crt_glue.pre_facts rc B API L A regs mem md PRE).
Local Abbreviation u_home := (@crt_glue.u_home rc B API L A regs mem md ua uk UB).
Local Abbreviation u_bounds := (@crt_glue.u_bounds rc B API L A regs mem md ua uk PRE UB).
Local Abbreviation u_cstr := (@crt_glue.u_cstr rc B API BSP L A regs mem md u us ua uk CU0 UB UL UR).
Local Abbreviation nm_nil := (@crt_glue.nm_nil u Lam).
Local Abbreviation nm_cons := (@crt_glue.nm_cons regs mem b u us Lam ua uk CU0 UR LEN BYUo).
Local Abbreviation frame_kept := (@crt_glue.frame_kept rc B API ERR L A regs mem md u SEG PRE LEN).
Local Abbreviation u_statics := (@crt_glue.u_statics rc B API SFA AX L A regs mem md u ua uk UB UL UR LEN).
Local Abbreviation guard_of_MR := (@crt_glue.guard_of_MR rc B API AX).
Local Abbreviation pre_k_of_inv := (@crt_glue.pre_k_of_inv rc B API L A regs mem md u SEG PRE LEN).
Local Abbreviation frame_post := (@crt_glue.frame_post rc B API ERR L A regs mem md u SEG PRE LEN).
Local Abbreviation zu := (@crt_glue.zu u).
Local Abbreviation nz := (@crt_glue.nz u).
Local Abbreviation szb := (@crt_glue.szb u).
Local Abbreviation QF := (@crt_glue.QF rc B API L A regs mem md b u Lam peak cnt).
Local Abbreviation fr := (@crt_glue.fr regs).
Local Abbreviation blk_ok := (@crt_glue.blk_ok rc B u).
Local Abbreviation bm := (@crt_glue.bm b u).
Local Abbreviation kmid := (@crt_glue.kmid rc B API L A regs mem md Lam).
Local Abbreviation at_p1 := (@crt_glue.at_p1 rc B API L A regs mem md b u Lam peak cnt).
Local Abbreviation at_p2 := (@crt_glue.at_p2 rc B API L A regs mem md b u Lam peak cnt).
Local Abbreviation at_p3 := (@crt_glue.at_p3 rc B API L A regs mem md b u Lam peak cnt).
Local Abbreviation at_p4 := (@crt_glue.at_p4 rc B API L A regs mem md b u Lam peak cnt).
Local Abbreviation at_head := (@crt_glue.at_head rc B API L A regs mem md b u Lam peak cnt).
Local Abbreviation at_t := (@crt_glue.at_t rc B API L A regs mem md b u Lam peak cnt).
Local Abbreviation at_exit := (@crt_glue.at_exit rc B API L A regs mem md b u Lam peak cnt).
Local Abbreviation pf_img_free_of := (@crt_glue.pf_img_free_of rc B u SEG).
Local Abbreviation blk_off_img := (@crt_glue.blk_off_img rc B u SEG LEN).
Local Abbreviation stk_norm_of := (@crt_glue.stk_norm_of rc B API L A regs mem md u PRE LEN SPT).
Local Abbreviation snp_env_of := (@crt_glue.snp_env_of rc B API GS AX L A regs mem md u SEG PRE RA0 LEN CS0 SPT).
Local Abbreviation uenv_of := (@crt_glue.uenv_of rc B API BSP L A regs mem md u us ua uk PRE CU0 UB UL UR LEN).
Local Abbreviation text_ok := (@crt_glue.text_ok rc B API SFA AX L A regs mem md b u LEN BY0 BYUo).
Local Abbreviation kmid_after := (@crt_glue.kmid_after rc B API SFA GS AX L A regs mem md u Lam SEG PRE LEN).
Local Abbreviation kmid_call := (@crt_glue.kmid_call rc B API L A regs mem md u Lam LEN).
Local Abbreviation len_zu := (@crt_glue.len_zu u).
Local Abbreviation rt_nk_le := (@crt_glue.rt_nk_le u LEN).
Local Abbreviation e_zu_cons := (@crt_glue.e_zu_cons u).
Local Abbreviation e_rt_cons := (@crt_glue.e_rt_cons regs mem b u us Lam peak cnt ua uk CU0 UR LEN BYUo).
Local Abbreviation cs_cases := (@crt_glue.cs_cases u LEN).
Local Abbreviation cs_post := (@crt_glue.cs_post u LEN).
Local Abbreviation t_regs := (@crt_glue.t_regs u LEN).
Local Abbreviation h_firstn_snoc := (@crt_glue.h_firstn_snoc u LEN).
Local Abbreviation h_fb_step := (@crt_glue.h_fb_step u LEN).
Local Abbreviation h_rt_p := (@crt_glue.h_rt_p u LEN).
Local Abbreviation h_rt_np := (@crt_glue.h_rt_np u LEN).
Local Abbreviation h_exit_regs := (@crt_glue.h_exit_regs regs u LEN).
Local Abbreviation h_at_exit := (@crt_glue.h_at_exit rc B API L A regs mem md b u Lam peak cnt).
Local Abbreviation e_kmid_call := (@crt_glue.e_kmid_call rc B API L A regs mem md u Lam LEN).

Definition nroom_cf (b1 : sbound) : Prop :=
  sb_live b1 + 1 <= sb_cap b1 <= CAP_AG /\ 0 <= sb_bytes b1 /\ sb_bytes b1 + (Z.of_nat (length u) + 19) <= 2 ^ 29.

Lemma room_m_cf : nroom_cf bm.
Proof. unfold nroom_cf, crt_glue.bm, sb_malloc, crt_glue.szb, crt_glue.nz. cbn [sb_live sb_bytes sb_cap]. lia. Qed.

Lemma room_b_cf : nroom_cf b.
Proof. unfold nroom_cf. lia. Qed.

Lemma names_glue_cf : forall blk (fx1 : FPState) L1 A1 regs1 mem1 md1 pk1 c1 b1 (tb ts : list byte) Q',
  crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 ->
  spZ regs1 = spZ regs - 112 -> YK0s.ret_ok (getr regs1 1) -> getr regs1 4 = getr regs 4 ->
  frm_zero (@fp_csr fx1) ->
  getr regs1 11 = getr regs 10 ->
  cstr_at mem1 (bv_unsigned (getr regs1 10)) tb ts ->
  str_home L1 A1 (bv_unsigned (getr regs1 10)) (Z.of_nat (length tb + 1)) ->
  4096 <= bv_unsigned (getr regs1 10) -> Z.of_nat (length tb) + 1 < 2 ^ 62 ->
  bv_unsigned (getr regs1 10) + Z.of_nat (length tb + 1 + length ts) <= alloc_ceiling + 8 ->
  off_statics (bv_unsigned (getr regs1 10)) (Z.of_nat (length tb + 1 + length ts)) ->
  alloc_words B mem1 (lsum Lam) pk1 c1 (2 ^ 64 - 1) -> lsum Lam <= pk1 < 2 ^ 64 -> 0 <= c1 -> c1 + 1 < 2 ^ 63 ->
  res_ok_slots A1 b1 -> nroom_cf b1 ->
  (forall (fx2 : FPState) L2 A2 regs2 mem2 md2,
     crt_inv B API CRT_K L A regs mem md blk L2 A2 mem2 md2 -> regs_preserved regs1 regs2 ->
     frm_zero (@fp_csr fx2) ->
     getr regs2 10 = Z_to_bv 64 (names (ManifestMem.zbytes tb) (ManifestMem.zbytes u)) ->
     alloc_words B mem2 (lsum Lam) (nm_pk pk1) (nm_c c1) (2 ^ 64 - 1) ->
     lsum Lam <= nm_pk pk1 < 2 ^ 64 ->
     res_ok_slots A2 b1 ->
     (forall a, spZ regs - 112 <= a < spZ regs ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
     SRcf B (mkCfg (@mkst fx2 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) Q') ->
  SRcf B (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 names_c.NAMES) mem1 (seg_rom (ms_segs B))) md1) Q'.
Proof.
  intros blk fx1 L1 A1 regs1 mem1 md1 pk1 c1 b1 tb ts Q' IV SP1 RA1 TP1 FRM1 R11 CT HT T4 LT TB OT AW PK C0 C1
    RES1 ROOM1 K.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & HWF1 & HBD1 & INIT1 & _ & _ & _ & _ & HSC & RA & GK).
  destruct (u_cstr blk L1 A1 mem1 md1 IV) as (us1 & CU1 & Lus1).
  destruct u_bounds as (UB1 & UB2).
  pose proof (ceil8_ge (bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1)) as Rus.
  pose proof QT as (QFq & QC0 & QC1).
  assert (LG1 : ledger B L1 A1 mem1 Lam pk1 c1 (2 ^ 64 - 1)).
  { eapply ledger_rebuild; [exact SEG | exact IV | exact LG | exact AW | lia | lia | lia]. }
  pose proof (guard_of_MR L1 A1 mem1 md1 HM1) as GC1.
  pose proof (img_strings_keep mem mem1 RA0 RA IMG) as IMG1.
  pose proof (u_statics blk L1 A1 mem1 md1 us1 IV Lus1) as OU.
  pose proof (u_home blk L1 A1 mem1 md1 IV) as UH1.
  assert (SPr : bv_unsigned (getr regs1 2) = spZ regs - 112) by exact SP1.
  eapply SRcf_bind.
  { apply (NCF fx1 L1 A1 regs1 mem1 md1 b1 tb ts u us1 Lam pk1 c1 (2 ^ 64 - 1)).
    - exact SEG.
    - apply (pre_k_of_inv blk); [exact IV | exact SP1 | exact RA1 | exact TP1 | rewrite namesk_val; lia].
    - exact INIT1.
    - rewrite SPr. lia.
    - exact FRM1.
    - exact RA.
    - exact GC1.
    - exact CT.
    - rewrite R11. exact CU1.
    - exact HT.
    - rewrite R11. left. exists ua, uk. split; [exact UH1|]. lia.
    - exact T4.
    - rewrite R11. lia.
    - exact LT.
    - exact LEN.
    - exact IMG1.
    - unfold off_stack. rewrite SPr, namesk_val. left. lia.
    - unfold off_stack. rewrite SPr, R11, namesk_val. left. lia.
    - unfold off_stack. rewrite SPr, namesk_val. unfold PREFIX_LC_STR. left. lia.
    - unfold off_stack. rewrite SPr, namesk_val. unfold PREFIX_UC_STR. left. lia.
    - unfold off_stack. rewrite SPr, namesk_val. unfold FMT_WHOLE_STR. left. lia.
    - exact OT.
    - rewrite R11. exact OU.
    - exact LG1.
    - exact RES1.
    - exact (proj1 ROOM1).
    - exact (proj1 (proj2 ROOM1)).
    - exact (proj2 (proj2 ROOM1)). }
  intros c' POST.
  destruct POST as (fx2 & L2 & A2 & regs2 & mem2 & md2 & res & -> & FRM2 & INIT2 & BP & RES10 & _ & _ & ARMS & SLOTS).
  pose proof BP as (_ & _ & _ & RP2 & _).
  apply (K fx2 L2 A2 regs2 mem2 md2).
  - eapply (inv_bpost B API) with (K1 := NAMES_K) (regs1 := regs1) (L1 := L1) (A1 := A1) (mem1 := mem1) (md1 := md1) (regs2 := regs2);
      first [exact SEG | exact AX | exact CTX | exact ERR | exact GS | exact IV | exact HM0 | exact BP | exact INIT2
            | rewrite ?SP1, ?crtk_val, ?namesk_val; lia].
  - exact RP2.
  - exact FRM2.
  - rewrite RES10. f_equal.
    destruct ARMS as [(Eub & Er & _) | [(_ & Ecf & _) | (_ & _ & Er & _)]].
    + rewrite Er, Eub. reflexivity.
    + lia.
    + exact Er.
  - destruct ARMS as [(Eub & Er & LG2) | [(_ & Ecf & _) | (Nub & _ & _ & LG2)]].
    + destruct (nm_nil Eub pk1 c1) as [-> ->]. exact (proj1 LG2).
    + lia.
    + destruct (nm_cons Nub pk1 c1) as [-> ->]. rewrite (Z.mod_small (c1 + 1) (2 ^ 64)) in LG2 by lia. exact (proj1 LG2).
  - destruct ARMS as [(Eub & Er & LG2) | [(_ & Ecf & _) | (Nub & _ & _ & LG2)]].
    + rewrite (proj1 (nm_nil Eub pk1 c1)). exact (proj1 (proj2 LG2)).
    + lia.
    + rewrite (proj1 (nm_cons Nub pk1 c1)). exact (proj1 (proj2 LG2)).
  - exact SLOTS.
  - apply (frame_kept NAMES_K stat_writes L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 BP HM1 SP1).
    intros a Ha. unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in Ha. lia.
Qed.

Lemma as_ruled_glue_cf : forall blk (fx1 : FPState) L1 A1 regs1 mem1 md1 pk1 c1 b1 (tb ts : list byte) Q',
  crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 ->
  spZ regs1 = spZ regs - 112 -> YK0s.ret_ok (getr regs1 1) -> getr regs1 4 = getr regs 4 ->
  frm_zero (@fp_csr fx1) ->
  getr regs1 11 = getr regs 10 ->
  cstr_at mem1 (bv_unsigned (getr regs1 10)) tb ts ->
  str_home L1 A1 (bv_unsigned (getr regs1 10)) (Z.of_nat (length tb + 1)) ->
  4096 <= bv_unsigned (getr regs1 10) -> Z.of_nat (length tb) + 1 < 2 ^ 62 ->
  bv_unsigned (getr regs1 10) + Z.of_nat (length tb + 1 + length ts) <= alloc_ceiling ->
  off_statics (bv_unsigned (getr regs1 10)) (Z.of_nat (length tb + 1 + length ts)) ->
  alloc_words B mem1 (lsum Lam) pk1 c1 (2 ^ 64 - 1) -> lsum Lam <= pk1 < 2 ^ 64 -> 0 <= c1 -> c1 + 1 < 2 ^ 63 ->
  res_ok_slots A1 b1 -> nroom_cf b1 ->
  (forall (fx2 : FPState) L2 A2 regs2 mem2 md2,
     crt_inv B API CRT_K L A regs mem md blk L2 A2 mem2 md2 -> regs_preserved regs1 regs2 ->
     frm_zero (@fp_csr fx2) ->
     alloc_words B mem2 (lsum Lam) (nm_pk pk1) (nm_c c1) (2 ^ 64 - 1) ->
     lsum Lam <= nm_pk pk1 < 2 ^ 64 ->
     res_ok_slots A2 b1 ->
     (forall a, spZ regs - 112 <= a < spZ regs ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
     SRcf B (mkCfg (@mkst fx2 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) Q') ->
  SRcf B (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 AS_RULED) mem1 (seg_rom (ms_segs B))) md1) Q'.
Proof.
  intros blk fx1 L1 A1 regs1 mem1 md1 pk1 c1 b1 tb ts Q' IV SP1 RA1 TP1 FRM1 R11 CT HT T4 LT TB OT AW PK C0 C1
    RES1 ROOM1 K.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & HWF1 & HBD1 & INIT1 & _ & _ & _ & _ & HSC & RA & GK).
  destruct (u_cstr blk L1 A1 mem1 md1 IV) as (us1 & CU1 & Lus1).
  destruct u_bounds as (UB1 & UB2).
  pose proof (ceil8_ge (bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1)) as Rus.
  pose proof QT as (QFq & QC0 & QC1).
  assert (LG1 : ledger B L1 A1 mem1 Lam pk1 c1 (2 ^ 64 - 1)).
  { eapply ledger_rebuild; [exact SEG | exact IV | exact LG | exact AW | lia | lia | lia]. }
  pose proof (guard_of_MR L1 A1 mem1 md1 HM1) as GC1.
  pose proof (img_strings_keep mem mem1 RA0 RA IMG) as IMG1.
  pose proof (u_statics blk L1 A1 mem1 md1 us1 IV Lus1) as OU.
  pose proof (u_home blk L1 A1 mem1 md1 IV) as UH1.
  assert (SPr : bv_unsigned (getr regs1 2) = spZ regs - 112) by exact SP1.
  eapply SRcf_bind.
  { apply (ACF fx1 L1 A1 regs1 mem1 md1 b1 tb ts u us1 Lam pk1 c1 (2 ^ 64 - 1)).
    - exact SEG.
    - apply (pre_k_of_inv blk); [exact IV | exact SP1 | exact RA1 | exact TP1 | rewrite asrk_val; lia].
    - exact INIT1.
    - rewrite SPr. lia.
    - exact FRM1.
    - exact RA.
    - exact GC1.
    - exact CT.
    - rewrite R11. exact CU1.
    - exact HT.
    - rewrite R11. left. exists ua, uk. split; [exact UH1|]. lia.
    - exact T4.
    - rewrite R11. lia.
    - exact LT.
    - exact LEN.
    - exact IMG1.
    - unfold off_stack. rewrite SPr, asrk_val. left. lia.
    - unfold off_stack. rewrite SPr, R11, asrk_val. left.
      assert (C8 : bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1 + Z.of_nat (length us1) <= alloc_ceiling).
      { rewrite Lus1. apply ceil8_le; [lia|]. destruct Hacv as [_ Hm]. Z.div_mod_to_equations. lia. }
      lia.
    - exact OT.
    - rewrite R11. exact OU.
    - exact LG1.
    - split; [reflexivity|]. lia.
    - exact RES1.
    - exact (proj1 ROOM1).
    - exact (proj1 (proj2 ROOM1)).
    - exact (proj2 (proj2 ROOM1)). }
  intros c' POST.
  destruct POST as (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & FRM2 & INIT2 & BP & _ & _ & ARMS & SLOTS).
  pose proof BP as (_ & _ & _ & RP2 & _).
  apply (K fx2 L2 A2 regs2 mem2 md2).
  - eapply (inv_bpost B API) with (K1 := AS_RULED_K) (regs1 := regs1) (L1 := L1) (A1 := A1) (mem1 := mem1) (md1 := md1) (regs2 := regs2);
      first [exact SEG | exact AX | exact CTX | exact ERR | exact GS | exact IV | exact HM0 | exact BP | exact INIT2
            | rewrite ?SP1, ?crtk_val, ?asrk_val; lia].
  - exact RP2.
  - exact FRM2.
  - destruct ARMS as [(Eub & LG2) | (Nub & LG2)].
    + destruct (nm_nil Eub pk1 c1) as [-> ->]. exact (proj1 LG2).
    + destruct (nm_cons Nub pk1 c1) as [-> ->]. exact (proj1 LG2).
  - destruct ARMS as [(Eub & LG2) | (Nub & LG2)].
    + rewrite (proj1 (nm_nil Eub pk1 c1)). exact (proj1 (proj2 LG2)).
    + rewrite (proj1 (nm_cons Nub pk1 c1)). exact (proj1 (proj2 LG2)).
  - exact SLOTS.
  - apply (frame_kept AS_RULED_K stat_writes L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 BP HM1 SP1).
    intros a Ha. unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in Ha. lia.
Qed.

Lemma malloc_glue_cf : forall (fx1 : FPState) L1 A1 regs1 mem1 md1 pk c b1 sz Q',
  crt_inv B API CRT_K L A regs mem md [] L1 A1 mem1 md1 ->
  spZ regs1 = spZ regs - 112 -> YK0s.ret_ok (getr regs1 1) -> getr regs1 4 = getr regs 4 ->
  getr regs1 10 = Z_to_bv 64 sz ->
  alloc_words B mem1 (lsum Lam) pk c (2 ^ 64 - 1) ->
  res_ok_slots A1 b1 -> room_ag b1 sz ->
  (forall L2 A2 regs2 mem2 md2 res,
     crt_inv B API CRT_K L A regs mem md [(res, sz)] L2 A2 mem2 md2 -> regs_preserved regs1 regs2 ->
     getr regs2 10 = Z_to_bv 64 res -> res mod 16 = 0 -> fresh_block B res sz ->
     alloc_words B mem2 (lsum Lam) pk c (2 ^ 64 - 1) ->
     res_ok_slots A2 (sb_malloc b1 sz) ->
     (forall a, spZ regs - 112 <= a < spZ regs ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
     SRcf B (mkCfg (@mkst fx1 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) Q') ->
  SRcf B (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x14ce0) mem1 (seg_rom (ms_segs B))) md1) Q'.
Proof.
  intros fx1 L1 A1 regs1 mem1 md1 pk c b1 sz Q' IV SP1 RA1 TP1 A10 AW RES1 ROOM1 K.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & RA & _).
  destruct MSO as [EM _]. rewrite <- EM.
  eapply SRcf_bind.
  { apply (MCF fx1 L1 A1 regs1 mem1 md1 sz b1).
    - apply call_pre_k_alloc. apply (pre_k_of_inv []); [exact IV | exact SP1 | exact RA1 | exact TP1 | unfold ALLOC_STACK; lia].
    - rewrite SEG. exact RA.
    - exact A10.
    - exact RES1.
    - exact (@room_cf_of rc B API LIMLAW L1 A1 mem1 md1 b1 sz HM1 ROOM1). }
  intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & CP & R10 & Rn & R16 & FB & SPL & BK & RA2 & GK2 & _ & INIT2 & _ & SLOTS).
  apply call_post_k_alloc in CP.
  pose proof CP as (_ & _ & _ & _ & _ & RP2 & _).
  apply (K L2 A2 regs2 mem2 md2 res).
  - eapply (inv_malloc B API) with (regs1 := regs1) (regs2 := regs2);
      first [exact SEG | exact AX | exact CTX | exact ERR | exact GS | exact IV | exact HM0 | exact CP | exact SPL
            | exact INIT2 | exact GK2 | (rewrite SEG in RA2; exact RA2)
            | (intros a k i Hin Hi; exact (BK a k i Hin (fun x => x) Hi))
            | rewrite ?SP1, ?crtk_val; unfold ALLOC_STACK; lia].
  - exact RP2.
  - exact R10.
  - exact R16.
  - exact FB.
  - eapply (aw_cpost B API SFA SF SNE); [exact AW | exact HM1 | exact CP | intros x _ []| rewrite SP1; unfold ALLOC_STACK; lia].
  - exact SLOTS.
  - apply (frame_post L1 A1 regs1 mem1 md1 (fun _ => False) L2 A2 regs2 mem2 md2 CP HM1 SP1). intros a [].
Qed.

Lemma free_glue_cf : forall (fx1 : FPState) L1 A1 regs1 mem1 md1 pk c b1 res sz Q',
  crt_inv B API CRT_K L A regs mem md [(res, sz)] L1 A1 mem1 md1 -> 0 < sz ->
  spZ regs1 = spZ regs -> YK0s.ret_ok (getr regs1 1) -> getr regs1 4 = getr regs 4 ->
  getr regs1 10 = Z_to_bv 64 res ->
  alloc_words B mem1 (lsum Lam) pk c (2 ^ 64 - 1) ->
  res_ok_slots A1 b1 ->
  (forall L2 A2 regs2 mem2 md2,
     crt_inv B API CRT_K L A regs mem md [] L2 A2 mem2 md2 -> regs_preserved regs1 regs2 ->
     alloc_words B mem2 (lsum Lam) pk c (2 ^ 64 - 1) ->
     res_ok_slots A2 (sb_free b1 sz) ->
     SRcf B (mkCfg (@mkst fx1 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) Q') ->
  SRcf B (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x14ba0) mem1 (seg_rom (ms_segs B))) md1) Q'.
Proof.
  intros fx1 L1 A1 regs1 mem1 md1 pk c b1 res sz Q' IV Hsz SP1 RA1 TP1 A10 AW RES1 K.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & HWF1 & HBD1 & INIT1 & _ & (c1 & c2 & Ec1 & _) & _ & _ & HSC & RA & _).
  assert (Hin : In (res, sz) (blocks L1 A1)) by exact (blk_in L1 A1 c1 [(res, sz)] c2 res sz Ec1 (or_introl eq_refl)).
  destruct (in_blocks L1 A1 res sz Hin) as (p & Hp & Ep).
  destruct MSO as [_ EF]. rewrite <- EF.
  eapply SRcf_bind.
  { apply (FCF fx1 L1 A1 regs1 mem1 md1 p sz b1).
    - unfold call_pre. split; [exact HM1|]. split; [exact HWF1|]. split; [exact HBD1|]. split; [exact RA1|].
      rewrite SP1. split; [exact H16|]. split; [unfold ALLOC_STACK; lia|]. split; [exact H63|].
      split; [intros a Ha; rewrite SEG; apply HSC; left; rewrite crtk_val; unfold ALLOC_STACK in Ha; lia|].
      split; [rewrite TP1; exact HTP|].
      split; [intros a Ha; rewrite SEG; apply HSC; right; exact Ha|].
      intros H. rewrite INIT1 in H. discriminate.
    - rewrite SEG. exact RA.
    - exact Hp.
    - rewrite <- Ep. exact A10.
    - exact RES1. }
  intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & CP & SPL & BK & RA2 & GK2 & _ & INIT2 & _ & SLOTS).
  pose proof CP as (_ & _ & _ & _ & _ & RP2 & _).
  rewrite <- Ep in CP, SPL, BK.
  apply (K L2 A2 regs2 mem2 md2).
  - eapply (inv_free B API) with (regs1 := regs1) (regs2 := regs2) (res := res) (sz := sz);
      first [exact SEG | exact AX | exact CTX | exact ERR | exact GS | exact IV | exact HM0 | exact CP | exact SPL
            | exact (INIT2 INIT1) | exact GK2 | exact Hsz | (rewrite SEG in RA2; exact RA2)
            | (intros a k i H1 H2 H3; exact (BK a k i H1 H2 H3))
            | rewrite ?SP1, ?crtk_val; unfold ALLOC_STACK; lia].
  - exact RP2.
  - eapply aw_cpost; first [exact SFA | exact SF | exact SNE | exact AW | exact HM1 | exact CP
                         | rewrite SP1; unfold ALLOC_STACK; lia | idtac].
    intros x Hx Hr. apply (static_not_block B API SFA AX L1 A1 mem1 md1 res sz (x - res) HM1 Hin); [lia|].
    replace (res + (x - res)) with x by lia. exact Hx.
  - exact SLOTS.
Qed.

Definition HeadK_cf (k m : nat) : Prop :=
  forall f R mem1 md1, at_head k m f R mem1 md1 ->
    SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.

Lemma st_p3_cf : (forall f R mem1 md1, at_p4 f R mem1 md1 ->
     SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x133bc) mem1 (seg_rom (ms_segs B))) md1) QF) ->
  forall f R mem1 md1, at_p3 f R mem1 md1 ->
    SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x13390) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros P4 f R mem1 md1 (L1 & A1 & res & FRM & BO & NE & KM & R10 & R9 & R18 & R19).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  assert (NL : (1 <= length u <= 255)%nat).
  { assert (length u <> 0)%nat by (intros H0; apply NE; apply length_zero_iff_nil; exact H0). lia. }
  eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_wx SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk).
    - exact R10.
    - exact R9.
    - exact R18.
    - exact NL.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13a38) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x133bc) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q9 : getr R2 9 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); exact R9).
  assert (Q18 : getr R2 18 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact R18).
  assert (Q19 : getr R2 19 = Z_to_bv 64 nz) by (rewrite <- (getr_eqv _ _ XR); exact R19).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact R18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 2) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold crt_glue.szb, crt_glue.nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_wholex (ManifestMem.zbytes u)) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite len_wholex, length_zb; unfold crt_glue.szb, crt_glue.nz; lia|].
  rewrite <- SEG.
  apply (as_ruled_glue_cf [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 2) bm
           (pf_bytes (txt_wholex (ManifestMem.zbytes u))) (skipn (length (txt_wholex (ManifestMem.zbytes u)) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. exact TB.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m_cf.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 AW3 PK3 SL FK.
    rewrite Q1. apply P4.
    destruct (nm_cons NE (nm_pk peak) (cnt + 2)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|]. split; [exact NE|].
    split; [replace (cnt + 3) with (cnt + 2 + 1) by lia; exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK)|].
    split; [transitivity (getr R2 9); [exact (RP 9 ltac:(unfold callee_saved; lia)) | exact Q9]|].
    split; [transitivity (getr R2 18); [exact (RP 18 ltac:(unfold callee_saved; lia)) | exact Q18]|].
    transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19].
Qed.

Definition PtK_cf (P : FPState -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) (pc : Z) : Prop :=
  forall f R mem1 md1, P f R mem1 md1 ->
    SRcf B (mkCfg (@mkst f R (Z_to_bv 64 pc) mem1 (seg_rom (ms_segs B))) md1) QF.

Lemma st_exit_cf : PtK_cf at_exit 0x14ba0.
Proof.
  intros f R mem1 md1 (L1 & A1 & res & FRM & BO & NE & IV & AW & PK & RES & SP & R10 & CS & R1).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof rt_nk_le as NK.
  destruct (e_rt_cons NE) as (EC & EP).
  apply (free_glue_cf f L1 A1 R mem1 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu)) bm res szb).
  - exact IV.
  - unfold crt_glue.szb, crt_glue.nz. lia.
  - exact SP.
  - rewrite R1. exact HRA.
  - exact (CS 4 ltac:(unfold callee_saved; lia)).
  - exact R10.
  - exact AW.
  - exact RES.
  - intros L2 A2 regs2 mem2 md2 IV2 RP AW2 RES2.
    pose proof IV2 as (_ & _ & _ & INIT2 & _).
    assert (RPa : regs_preserved regs regs2).
    { intros r Hr. transitivity (getr R (Z_to_bv 5 r)); [exact (RP r Hr) | exact (CS r Hr)]. }
    rewrite R1. apply SRcf_ret. unfold crt_glue.QF, crt_post.
    exists f, L2, A2, regs2, mem2, md2.
    split; [reflexivity|].
    split; [exact FRM|].
    split; [exact INIT2|].
    split; [eapply (bpost_of_inv B API); first [exact SEG | exact IV2 | exact RPa]|].
    split; [destruct (u_cstr [] L2 A2 mem2 md2 IV2) as (us1 & CU1 & _); exists us1; exact CU1|].
    change (ManifestMem.zbytes u) with zu.
    split.
    + rewrite EP, EC.
      replace (cnt + (3 + 4 * Z.of_nat (rt_nk zu))) with (cnt + 3 + 4 * Z.of_nat (rt_nk zu)) by lia.
      eapply ledger_rebuild; [exact SEG | exact IV2 | exact LG | exact AW2 | lia | lia | lia].
    + unfold crt_glue.bm in RES2. rewrite sb_free_malloc in RES2. exact RES2.
Qed.

Lemma exit_cont_cf : forall s ms' (Fx : bvmap 5 word) (fcx : bv 32) (sp0 : Z)
    (gp tp t0 t1 t2 r10 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) R mem1 md1 L1 A1 res c b1,
  ms_rel_cj rsegs s (exit_state (getr regs 1) sp0 gp tp t0 t1 t2 (getr regs 8) (getr regs 9) r10 a1 a2 a3 a4 a5 a6 a7
    (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
    (getr regs 25) (getr regs 26) (getr regs 27) t3 t4 t5 t6 Fx fcx (normalize_cj rsegs mem1)) ->
  cj_same rsegs mem1 (ms_mem s) -> ms_eqv s ms' ->
  PtK_cf at_exit 0x14ba0 -> frm_zero fcx -> blk_ok res -> u <> [] ->
  kmid [(res, szb)] L1 A1 R mem1 md1 (nm_pk peak) c b1 ->
  sp0 = spZ regs - 112 -> gp = getr regs 3 -> tp = getr regs 4 -> r10 = Z_to_bv 64 res ->
  c = cnt + 3 + 4 * Z.of_nat (rt_nk zu) -> b1 = bm ->
  SRcf B (mkCfg ms' md1) QF.
Proof.
  intros s ms' Fx fcx sp0 gp tp t0 t1 t2 r10 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 R mem1 md1 L1 A1 res c b1
    REL ROS EQV EX FRM BO NE KM -> -> -> -> -> ->.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & _ & AW & PK & RES).
  pose proof IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RA1 & _).
  destruct pre_facts as (HAC & H63 & _).
  unfold exit_state in REL.
  destruct (ka_post s _ Fx (Z_to_bv 64 0x14ba0) fcx (normalize_cj rsegs mem1) ms' mem1 [] REL ROS EQV RA1
    (munch_refl _ _) (wmono_refl _ _)) as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (KM2 : kmid [(res, szb)] L1 A1 R mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu))
                  bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R mem2 [] KM MU2 WM2 RA2); try assumption.
    intros x Hx O. exfalso. apply O. exact I. }
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  rewrite <- SEG. apply (EX (mkFP Fx fcx) R2 mem2 md1).
  exists L1, A1, res. split; [exact FRM|]. split; [exact BO|]. split; [exact NE|].
  split; [exact IV2|]. split; [exact AW2|]. split; [exact PK2|]. split; [exact RES2|].
  split.
  { unfold spZ at 1. rewrite <- (getr_eqv _ _ XR).
    change (bv_unsigned (Z_to_bv 64 (spZ regs - 112 + 112)) = spZ regs).
    replace (spZ regs - 112 + 112) with (spZ regs) by lia. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
  split; [|rewrite <- (getr_eqv _ _ XR); reflexivity].
  intros r Hr. rewrite <- (getr_eqv _ _ XR (Z_to_bv 5 r)). unfold callee_saved in Hr.
  assert (HC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct HC as [-> | HC].
  - change (Z_to_bv 64 (spZ regs - 112 + 112) = getr regs (Z_to_bv 5 2)).
    replace (spZ regs - 112 + 112) with (spZ regs) by lia. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]];
      reflexivity.
Qed.

Lemma st_t4_cf : PtK_cf at_exit 0x14ba0 -> forall k m, HeadK_cf (S k) (S m) -> PtK_cf (at_t 4 k m) 0x134b4.
Proof.
  intros EX k m HK f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & BR & FMT & R25 & R26 & R27 & _ & FA & PN & CNT).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof BR as (R9 & R18 & R19 & R24 & Hk & HL & S0p & S0b).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct (Nat.lt_ge_cases (S k) (length u)) as [LT|GE].
  - eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_next with (n := Z.of_nat (length u)) (k := Z.of_nat k).
      - exact R19.
      - exact R24.
      - exact R25.
      - lia.
      - lia.
      - lia.
      - exact S0b. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    destruct (ka_post s _ _ (Z_to_bv 64 0x133f4) _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
      as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
    set (mem2 := ms_mem s) in *.
    assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
    assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
    assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
    assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
    assert (H8 : getr R2 8 = getr R 8) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
    assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 4)
                    bm).
    { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 [] KM MU2 WM2 RA2); try assumption.
      intros x Hx O. exfalso. apply O. exact I. }
    rewrite <- SEG. apply (HK _ R2 mem2 md1).
    exists L1, A1, res. split; [exact FRM|]. split; [exact BO|].
    split.
    { replace (cnt + 3 + 4 * Z.of_nat (S m)) with (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 4) by lia.
      replace (2 + 4 * S m)%nat with (2 + 4 * m + 4)%nat by lia. exact KM2. }
    split.
    { unfold head_regs. rewrite H8.
      split; [rewrite <- (getr_eqv _ _ XR); rewrite Nat2Z.inj_succ; reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); rewrite Nat2Z.inj_succ; reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); rewrite Nat2Z.inj_succ; reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); exact R26|].
      split; [rewrite <- (getr_eqv _ _ XR); exact R27|].
      split; [lia|]. split; [lia|]. split; [exact S0p | exact S0b]. }
    split; [rewrite <- (getr_eqv _ _ XR); exact R9|].
    split; [rewrite <- (getr_eqv _ _ XR); exact R18|].
    split.
    { destruct FMT as (F20 & F21 & F22 & F23). unfold fmt_regs. rewrite <- !(getr_eqv _ _ XR).
      exact (conj F20 (conj F21 (conj F22 F23))). }
    split.
    { replace (length u - S k + 1)%nat with (length u - k)%nat by lia. lia. }
    replace (S k - 1)%nat with k by lia. exact FA.
  - assert (NE : u <> []) by (intros E; rewrite E in Hk; cbn in Hk; lia).
    assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ R) (fr j)).
    { rewrite S1. apply rw_cells_normalize; [exact RA1 | exact FR |]. intros x Hx.
      cbn [crt_glue.fr frame_cells cells_size csize] in Hx. right. lia. }
    assert (RU : rt_used zu (S k) (length u - k) = 0%nat).
    { replace (length u - k)%nat with 1%nat by lia. cbn [rt_used]. rewrite len_zu.
      replace ((S k <? length u)%nat) with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. }
    assert (NK : rt_nk zu = S m) by lia.
    eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_last with (n := Z.of_nat (length u)) (k := Z.of_nat k).
      - exact R25.
      - lia.
      - lia.
      - lia.
      - exact FRn.
      - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    eapply exit_cont_cf; [exact REL | exact ROS | exact EQV | exact EX | exact FRM | exact BO | exact NE | exact KM
      | exact S1 | exact G3 | exact G4 | exact R18 | rewrite NK; lia | reflexivity].
Qed.

Lemma st_t3_cf : forall k m, PtK_cf (at_t 4 k m) 0x134b4 -> PtK_cf (at_t 3 k m) 0x13488.
Proof.
  intros k m P4. unfold PtK_cf in P4.
  intros f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & BR & FM & R25 & R26 & R27 & R10i & FA & PN & CNT).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof rt_nk_le as NKL.
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  pose proof BR as (B9 & B18 & B19 & B24 & Hk & Hu & HU0 & HU1).
  pose proof FM as (F20 & F21 & F22 & F23).
  assert (NE : u <> []) by (intros E; apply length_zero_iff_nil in E; lia).
  assert (LK : (k <= length (ManifestMem.zbytes u))%nat) by (rewrite length_zb; lia).
  eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_t1x SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk) (k := k).
    - exact BR.
    - exact (R10i ltac:(lia)).
    - exact R26.
    - exact F23.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13a38) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  pose proof (cs_post R R2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as CS.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x134b4) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact B18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold crt_glue.szb, crt_glue.nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_t1x (ManifestMem.zbytes u) k) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite (len_t1x _ _ LK), length_zb; unfold crt_glue.szb, crt_glue.nz; lia|].
  rewrite <- SEG.
  apply (as_ruled_glue_cf [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3)
           bm (pf_bytes (txt_t1x (ManifestMem.zbytes u) k))
           (skipn (length (txt_t1x (ManifestMem.zbytes u) k) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. exact TB.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m_cf.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 AW3 PK3 SL FK.
    rewrite Q1. apply P4.
    destruct (nm_cons NE (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    assert (CS2 : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r))
      by (intros r Hr; exact (eq_trans (RP r Hr) (CS r Hr))).
    destruct (t_regs R regs2 k res CS2 BR FM R25 R26 R27) as (BR2 & FM2 & E25 & E26 & E27).
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|].
    split.
    { replace (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 4) with (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3 + 1) by lia.
      replace (2 + 4 * m + 4)%nat with (S (2 + 4 * m + 3)) by lia.
      exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK). }
    split; [exact BR2|]. split; [exact FM2|]. split; [exact E25|]. split; [exact E26|]. split; [exact E27|].
    split; [intros H4; lia|].
    split; [exact FA|]. split; [exact PN | exact CNT].
Qed.

Lemma st_t2_cf : forall k m, PtK_cf (at_t 3 k m) 0x13488 -> PtK_cf (at_t 2 k m) 0x1345c.
Proof.
  intros k m P3. unfold PtK_cf in P3.
  intros f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & BR & FM & R25 & R26 & R27 & R10i & FA & PN & CNT).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof rt_nk_le as NKL.
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  pose proof BR as (B9 & B18 & B19 & B24 & Hk & Hu & HU0 & HU1).
  pose proof FM as (F20 & F21 & F22 & F23).
  assert (NE : u <> []) by (intros E; apply length_zero_iff_nil in E; lia).
  assert (LK : (k <= length (ManifestMem.zbytes u))%nat) by (rewrite length_zb; lia).
  eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_t3 SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk) (k := k).
    - exact BR.
    - exact (R10i ltac:(lia)).
    - exact R26.
    - exact F22.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13c1c) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  pose proof (cs_post R R2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as CS.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x13488) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact B18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold crt_glue.szb, crt_glue.nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_t3 (ManifestMem.zbytes u) k) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite (len_t3 _ _ LK), length_zb; unfold crt_glue.szb, crt_glue.nz; lia|].
  assert (ZF : Forall (fun c => 0 <= c < 256) (txt_t3 (ManifestMem.zbytes u) k)).
  { eapply Forall_impl; [|exact (nz_t3 _ k (zb_nz u (proj1 (proj2 CU1))))]. intros c Hc. cbv beta in Hc |- *. lia. }
  rewrite <- SEG.
  apply (names_glue_cf [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2)
           bm (pf_bytes (txt_t3 (ManifestMem.zbytes u) k))
           (skipn (length (txt_t3 (ManifestMem.zbytes u) k) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. lia.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m_cf.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10' AW3 PK3 SL FK.
    rewrite Q1. apply P3.
    destruct (nm_cons NE (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    assert (CS2 : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r))
      by (intros r Hr; exact (eq_trans (RP r Hr) (CS r Hr))).
    destruct (t_regs R regs2 k res CS2 BR FM R25 R26 R27) as (BR2 & FM2 & E25 & E26 & E27).
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|].
    split.
    { replace (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3) with (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2 + 1) by lia.
      replace (2 + 4 * m + 3)%nat with (S (2 + 4 * m + 2)) by lia.
      exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK). }
    split; [exact BR2|]. split; [exact FM2|]. split; [exact E25|]. split; [exact E26|]. split; [exact E27|].
    split.
    { intros _. rewrite R10', (zbytes_pf _ ZF). f_equal. apply rt_t3; [rewrite length_zb; lia | exact FA | exact PN]. }
    split; [exact FA|]. split; [exact PN | exact CNT].
Qed.

Lemma st_t1_cf : forall k m, PtK_cf (at_t 2 k m) 0x1345c -> PtK_cf (at_t 1 k m) 0x13430.
Proof.
  intros k m P2. unfold PtK_cf in P2.
  intros f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & BR & FM & R25 & R26 & R27 & R10i & FA & PN & CNT).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof rt_nk_le as NKL.
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  pose proof BR as (B9 & B18 & B19 & B24 & Hk & Hu & HU0 & HU1).
  pose proof FM as (F20 & F21 & F22 & F23).
  assert (NE : u <> []) by (intros E; apply length_zero_iff_nil in E; lia).
  assert (LK : (k <= length (ManifestMem.zbytes u))%nat) by (rewrite length_zb; lia).
  eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_t2 SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk) (k := k).
    - exact BR.
    - exact (R10i ltac:(lia)).
    - exact R26.
    - exact F21.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13c1c) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  pose proof (cs_post R R2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as CS.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x1345c) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact B18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 1) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold crt_glue.szb, crt_glue.nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_t2 (ManifestMem.zbytes u) k) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite (len_t2 _ _ LK), length_zb; unfold crt_glue.szb, crt_glue.nz; lia|].
  assert (ZF : Forall (fun c => 0 <= c < 256) (txt_t2 (ManifestMem.zbytes u) k)).
  { eapply Forall_impl; [|exact (nz_t2 _ k (zb_nz u (proj1 (proj2 CU1))))]. intros c Hc. cbv beta in Hc |- *. lia. }
  rewrite <- SEG.
  apply (names_glue_cf [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 1)
           bm (pf_bytes (txt_t2 (ManifestMem.zbytes u) k))
           (skipn (length (txt_t2 (ManifestMem.zbytes u) k) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. lia.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m_cf.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10' AW3 PK3 SL FK.
    rewrite Q1. apply P2.
    destruct (nm_cons NE (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 1)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    assert (CS2 : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r))
      by (intros r Hr; exact (eq_trans (RP r Hr) (CS r Hr))).
    destruct (t_regs R regs2 k res CS2 BR FM R25 R26 R27) as (BR2 & FM2 & E25 & E26 & E27).
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|].
    split.
    { replace (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2) with (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 1 + 1) by lia.
      replace (2 + 4 * m + 2)%nat with (S (2 + 4 * m + 1)) by lia.
      exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK). }
    split; [exact BR2|]. split; [exact FM2|]. split; [exact E25|]. split; [exact E26|]. split; [exact E27|].
    split.
    { intros _. rewrite R10', (zbytes_pf _ ZF). f_equal. apply rt_t2; [rewrite length_zb; lia | exact FA | exact PN]. }
    split; [exact FA|]. split; [exact PN | exact CNT].
Qed.

Lemma h_gt_cf : PtK_cf at_exit 0x14ba0 -> forall k m f R mem1 md1, at_head k m f R mem1 md1 ->
  byte_at zu (k - 1) = 62 ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros EX k m f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & HR & R9 & R18 & FM & CNT & FB) BG.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  pose proof UE as (CUn & _).
  pose proof HR as (E3 & E8 & E9 & E10 & E11 & Hk & Hu & H0 & H256).
  assert (NE : u <> []) by (intros E; rewrite E in Hk; cbn in Hk; lia).
  replace (length u - k + 1)%nat with (S (length u - k)) in CNT by lia.
  rewrite (h_rt_gt zu k (length u - k) BG) in CNT.
  assert (Em : m = rt_nk zu) by lia. subst m.
  assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ regs - 112) (fr j)).
  { apply rw_cells_normalize; [exact RA1 | exact FR |]. intros x Hx. cbn [crt_glue.fr frame_cells cells_size csize] in Hx.
    right. lia. }
  eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply crt_gt with (u := u) (us := us1) (j := j) (k := k)
      (xs0 := getr regs 8) (xs1 := getr regs 9) (xs2 := getr regs 18) (xs3 := getr regs 19) (xs4 := getr regs 20)
      (xs5 := getr regs 21) (xs6 := getr regs 22) (xs7 := getr regs 23) (xs8 := getr regs 24) (xs9 := getr regs 25)
      (xs10 := getr regs 26) (xs11 := getr regs 27) (xra := getr regs 1).
    - exact HR.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact CUn.
    - exact BG.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact FRn.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
  intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0. unfold exit_state in REL.
  destruct (ka_post s _ _ _ _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  destruct (h_exit_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R2 S1 G3 G4 XR) as (S2 & R10 & CS & R1).
  assert (KM2 : kmid [(res, szb)] L1 A1 R (ms_mem s) md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu))
                  bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R (ms_mem s) [] KM MU2 WM2 RA2); try assumption.
    intros x _ O. exfalso. apply O. exact I. }
  rewrite <- SEG. apply EX.
  apply (h_at_exit _ R R2 (ms_mem s) md1 L1 A1 res); [exact FRM | exact BO | exact NE | exact KM2 | exact S2 | | exact CS | exact R1].
  rewrite R10. exact R18.
Qed.

Lemma h_np_last_cf : PtK_cf at_exit 0x14ba0 -> forall k m f R mem1 md1, at_head k m f R mem1 md1 ->
  byte_at zu (k - 1) <> 62 -> plain_name (skipn k zu) = false -> (k + 1 = length u)%nat ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros EX k m f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & HR & R9 & R18 & FM & CNT & FB) BN PN HL.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  pose proof UE as (CUn & U0 & ULo & _).
  pose proof HR as (E3 & E8 & E9 & E10 & E11 & Hk & Hu & H0 & H256).
  assert (NE : u <> []) by (intros E; rewrite E in Hk; cbn in Hk; lia).
  replace (length u - k + 1)%nat with (S (S O)) in CNT by lia.
  rewrite (h_rt_np zu k 1 ltac:(rewrite len_zu; lia) BN PN) in CNT.
  rewrite (h_rt_end zu (S k) 1 ltac:(rewrite len_zu; lia)) in CNT.
  assert (Em : m = rt_nk zu) by lia. subst m.
  assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ regs - 112) (fr j)).
  { apply rw_cells_normalize; [exact RA1 | exact FR |]. intros x Hx. cbn [crt_glue.fr frame_cells cells_size csize] in Hx.
    right. lia. }
  eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_np_last PLN) with (lo := spZ regs - 8560) (u := u) (us := us1) (j := j) (k := k)
      (xs0 := getr regs 8) (xs1 := getr regs 9) (xs2 := getr regs 18) (xs3 := getr regs 19) (xs4 := getr regs 20)
      (xs5 := getr regs 21) (xs6 := getr regs 22) (xs7 := getr regs 23) (xs8 := getr regs 24) (xs9 := getr regs 25)
      (xs10 := getr regs 26) (xs11 := getr regs 27) (xra := getr regs 1).
    - exact HR.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact CUn.
    - exact BN.
    - exact PN.
    - exact HL.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact (stk_norm_of _ _ _ _ _ IV).
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia.
    - apply mem_inv_normalize.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact ULo.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact FRn.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI).
  subst s0. unfold exit_state in REL.
  destruct (ka_post s _ _ _ _ _ ms' mem1 _ REL ROS EQV RA1 MU WM) as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  destruct (h_exit_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R2 S1 G3 G4 XR) as (S2 & R10 & CS & R1).
  assert (KM2 : kmid [(res, szb)] L1 A1 R (ms_mem s) md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu))
                  bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R (ms_mem s) _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O. left. lia. }
  rewrite <- SEG. apply EX.
  apply (h_at_exit _ R R2 (ms_mem s) md1 L1 A1 res); [exact FRM | exact BO | exact NE | exact KM2 | exact S2 | | exact CS | exact R1].
  rewrite R10. exact R18.
Qed.

Lemma h_np_next_cf : forall k m, HeadK_cf (S k) m -> forall f R mem1 md1, at_head k m f R mem1 md1 ->
  byte_at zu (k - 1) <> 62 -> plain_name (skipn k zu) = false -> (k + 1 < length u)%nat ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros k m HK f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & HR & R9 & R18 & FM & CNT & FB) BN PN HL.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  pose proof UE as (CUn & U0 & ULo & _).
  pose proof HR as (E3 & E8 & E9 & E10 & E11 & Hk & Hu & H0 & H256).
  replace (length u - k + 1)%nat with (S (length u - k)) in CNT by lia.
  rewrite (h_rt_np zu k (length u - k) ltac:(rewrite len_zu; lia) BN PN) in CNT.
  eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_np_next PLN) with (lo := spZ regs - 8560) (u := u) (us := us1) (k := k).
    - exact HR.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact CUn.
    - exact BN.
    - exact PN.
    - exact HL.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact (stk_norm_of _ _ _ _ _ IV).
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia.
    - apply mem_inv_normalize.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact ULo. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI).
  subst s0.
  destruct (ka_post s _ _ _ _ _ ms' mem1 _ REL ROS EQV RA1 MU WM) as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O. left. lia. }
  rewrite <- SEG. apply HK.
  exists L1, A1, res. split; [exact FRM|]. split; [exact BO|]. split; [exact KM2|].
  split.
  { unfold head_regs. rewrite <- !(getr_eqv _ _ XR).
    refine (conj eq_refl (conj eq_refl (conj eq_refl (conj E10 (conj E11 (conj _ (conj Hu (conj H0 H256)))))))).
    lia. }
  split; [rewrite <- (getr_eqv _ _ XR); exact R9|].
  split; [rewrite <- (getr_eqv _ _ XR); exact R18|].
  split; [unfold fmt_regs; rewrite <- !(getr_eqv _ _ XR); exact FM|].
  split; [replace (length u - S k + 1)%nat with (length u - k)%nat by lia; exact CNT|].
  replace (S k - 1)%nat with k by lia.
  apply h_fb_step; [rewrite len_zu; lia | exact FB | exact BN].
Qed.

Lemma h_t1_cf : forall k m, PtK_cf (at_t 1 k m) 0x13430 -> forall f R mem1 md1, at_head k m f R mem1 md1 ->
  byte_at zu (k - 1) <> 62 -> plain_name (skipn k zu) = true ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros k m TK f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & HR & R9 & R18 & FM & CNT & FB) BN PN.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  pose proof HR as (E3 & E8 & E9 & E10 & E11 & Hk & Hu & H0 & H256).
  assert (NE : u <> []) by (intros E; rewrite E in Hk; cbn in Hk; lia).
  pose proof FM as (F20 & F21 & F22 & F23).
  replace (length u - k + 1)%nat with (S (length u - k)) in CNT by lia.
  rewrite (h_rt_p zu k (length u - k) ltac:(rewrite len_zu; lia) BN PN) in CNT.
  pose proof rt_nk_le as NK.
  assert (FBk : forallb (fun c => negb (c =? 62)) (firstn k zu) = true)
    by (apply h_fb_step; [rewrite len_zu; lia | exact FB | exact BN]).
  eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_t1 PLN SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk) (k := k).
    - exact HR.
    - exact R9.
    - exact R18.
    - exact F20.
    - exact BN.
    - exact PN.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13c1c) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x13430) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr R 8) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q8' : getr R2 8 = getr regs 10) by (rewrite Q8; exact G8).
  assert (Q9 : getr R2 9 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); exact R9).
  assert (Q18 : getr R2 18 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact R18).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact R18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q19 : getr R2 19 = getr R 19) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q20 : getr R2 20 = Z_to_bv 64 0x1035d) by (rewrite <- (getr_eqv _ _ XR); exact F20).
  assert (Q21 : getr R2 21 = Z_to_bv 64 0x1041d) by (rewrite <- (getr_eqv _ _ XR); exact F21).
  assert (Q22 : getr R2 22 = Z_to_bv 64 0x103bf) by (rewrite <- (getr_eqv _ _ XR); exact F22).
  assert (Q23 : getr R2 23 = Z_to_bv 64 0x10391) by (rewrite <- (getr_eqv _ _ XR); exact F23).
  assert (Q24 : getr R2 24 = getr R 24) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q25 : getr R2 25 = getr R 25) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q26 : getr R2 26 = getr R 26) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q27 : getr R2 27 = getr R 27) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold crt_glue.szb, crt_glue.nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_t1 (ManifestMem.zbytes u) k) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite len_t1, length_zb by (rewrite length_zb; lia); unfold crt_glue.szb, crt_glue.nz; lia|].
  rewrite <- SEG.
  apply (names_glue_cf [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m) bm
           (pf_bytes (txt_t1 (ManifestMem.zbytes u) k)) (skipn (length (txt_t1 (ManifestMem.zbytes u) k) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. lia.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m_cf.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10' AW3 PK3 SL FK.
    rewrite Q1. apply TK.
    destruct (nm_cons NE (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    assert (P8 : getr regs2 8 = getr R 8)
      by (transitivity (getr R2 8); [exact (RP 8 ltac:(unfold callee_saved; lia)) | exact Q8]).
    assert (P9 : getr regs2 9 = Z_to_bv 64 szb)
      by (transitivity (getr R2 9); [exact (RP 9 ltac:(unfold callee_saved; lia)) | exact Q9]).
    assert (P18 : getr regs2 18 = Z_to_bv 64 res)
      by (transitivity (getr R2 18); [exact (RP 18 ltac:(unfold callee_saved; lia)) | exact Q18]).
    assert (P19 : getr regs2 19 = getr R 19)
      by (transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19]).
    assert (P20 : getr regs2 20 = Z_to_bv 64 0x1035d)
      by (transitivity (getr R2 20); [exact (RP 20 ltac:(unfold callee_saved; lia)) | exact Q20]).
    assert (P21 : getr regs2 21 = Z_to_bv 64 0x1041d)
      by (transitivity (getr R2 21); [exact (RP 21 ltac:(unfold callee_saved; lia)) | exact Q21]).
    assert (P22 : getr regs2 22 = Z_to_bv 64 0x103bf)
      by (transitivity (getr R2 22); [exact (RP 22 ltac:(unfold callee_saved; lia)) | exact Q22]).
    assert (P23 : getr regs2 23 = Z_to_bv 64 0x10391)
      by (transitivity (getr R2 23); [exact (RP 23 ltac:(unfold callee_saved; lia)) | exact Q23]).
    assert (P24 : getr regs2 24 = getr R 24)
      by (transitivity (getr R2 24); [exact (RP 24 ltac:(unfold callee_saved; lia)) | exact Q24]).
    assert (P25 : getr regs2 25 = getr R 25)
      by (transitivity (getr R2 25); [exact (RP 25 ltac:(unfold callee_saved; lia)) | exact Q25]).
    assert (P26 : getr regs2 26 = getr R 26)
      by (transitivity (getr R2 26); [exact (RP 26 ltac:(unfold callee_saved; lia)) | exact Q26]).
    assert (P27 : getr regs2 27 = getr R 27)
      by (transitivity (getr R2 27); [exact (RP 27 ltac:(unfold callee_saved; lia)) | exact Q27]).
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|].
    split.
    { replace (2 + 4 * m + 1)%nat with (S (2 + 4 * m)) by lia.
      exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK). }
    split.
    { unfold body_regs. rewrite P8, P9, P18, P19, P24.
      exact (conj eq_refl (conj eq_refl (conj E3 (conj E8 (conj Hk (conj Hu (conj H0 H256))))))). }
    split; [unfold fmt_regs; rewrite P20, P21, P22, P23; exact (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))|].
    split; [rewrite P25; exact E9|].
    split; [rewrite P26; exact E10|].
    split; [rewrite P27; exact E11|].
    split.
    { intros _. rewrite R10'. f_equal. rewrite zbytes_pf.
      - apply rt_t1; [rewrite length_zb; lia | exact FBk | exact PN].
      - eapply Forall_impl; [|apply nz_t1; apply zbytes_nz; exact (proj1 (proj2 CU1))]. intros c Hc. cbv beta in Hc |- *. lia. }
    split; [exact FBk|]. split; [exact PN|]. lia.
Qed.

Lemma st_head_cf : PtK_cf at_exit 0x14ba0 -> (forall k m, HeadK_cf (S k) (S m) -> PtK_cf (at_t 1 k m) 0x13430) ->
  forall k m, HeadK_cf k m.
Proof.
  intros EX T1.
  assert (IND : forall n k m, (length u - k = n)%nat -> HeadK_cf k m).
  { induction n as [|n IH]; intros k m En f R mem1 md1 HD.
    - exfalso. destruct HD as (L1 & A1 & res & _ & _ & _ & (_ & _ & _ & _ & _ & Hk & _) & _). lia.
    - pose proof HD as (L1 & A1 & res & _ & _ & _ & (_ & _ & _ & _ & _ & Hk & _) & _).
      destruct (Z.eq_dec (byte_at zu (k - 1)) 62) as [BG|BN].
      + exact (h_gt_cf EX k m f R mem1 md1 HD BG).
      + destruct (plain_name (skipn k zu)) eqn:PN.
        * exact (h_t1_cf k m (T1 k m (IH (S k) (S m) ltac:(lia))) f R mem1 md1 HD BN PN).
        * destruct (Nat.eq_dec (k + 1) (length u)) as [HL|HL].
          -- exact (h_np_last_cf EX k m f R mem1 md1 HD BN PN HL).
          -- exact (h_np_next_cf k m (IH (S k) m ltac:(lia)) f R mem1 md1 HD BN PN ltac:(lia)). }
  intros k m. exact (IND _ k m eq_refl).
Qed.

Lemma st_p4_cf : PtK_cf at_exit 0x14ba0 -> HeadK_cf 1 0 -> PtK_cf at_p4 0x133bc.
Proof.
  intros EX HK f R mem1 md1 (L1 & A1 & res & FRM & BO & NE & KM & R9 & R18 & R19).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct u_bounds as (UB1 & UB2).
  assert (NL : (1 <= length u <= 255)%nat).
  { assert (length u <> 0)%nat by (intros H0; apply NE; apply length_zero_iff_nil; exact H0). lia. }
  destruct (Nat.eq_dec (length u) 1) as [E1|E1].
  - assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ R) (fr j)).
    { rewrite S1. apply rw_cells_normalize; [exact RA1 | exact FR |]. intros x Hx.
      cbn [crt_glue.fr frame_cells cells_size csize] in Hx. right. lia. }
    assert (NK : rt_nk zu = 0%nat).
    { unfold rt_nk. rewrite len_zu, E1. cbn [rt_used]. rewrite len_zu, E1. reflexivity. }
    assert (R19' : getr R 19 = Z_to_bv 64 1) by (rewrite R19; unfold crt_glue.nz; rewrite E1; reflexivity).
    eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_init1.
      - exact R19'.
      - exact FRn.
      - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    eapply exit_cont_cf; [exact REL | exact ROS | exact EQV | exact EX | exact FRM | exact BO | exact NE | exact KM
      | exact S1 | exact G3 | exact G4 | exact R18 | rewrite NK; lia | reflexivity].
  - eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_init with (n := Z.of_nat (length u)).
      - exact R19.
      - lia.
      - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. lia. }
    intros s s0 P0 REL ROS ms' EQV.
    destruct P0 as (a0' & a1' & a2' & a3' & E0). subst s0.
    destruct (ka_post s _ _ (Z_to_bv 64 0x133f4) _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
      as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
    set (mem2 := ms_mem s) in *.
    assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
    assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
    assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
    assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
    assert (H19 : getr R2 19 = Z_to_bv 64 (bv_unsigned (getr R2 8) + Z.of_nat 1))
      by (rewrite <- !(getr_eqv _ _ XR); reflexivity).
    assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3) bm).
    { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 [] KM MU2 WM2 RA2); try assumption.
      intros x Hx O. exfalso. apply O. exact I. }
    rewrite <- SEG. apply (HK _ R2 mem2 md1).
    exists L1, A1, res. split; [exact FRM|]. split; [exact BO|].
    split; [replace (cnt + 3 + 4 * Z.of_nat 0) with (cnt + 3) by lia; exact KM2|].
    split.
    { unfold head_regs.
      split; [exact H19|].
      split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
      split; [lia|]. split; [lia|]. rewrite Q8. split; lia. }
    split; [rewrite <- (getr_eqv _ _ XR); exact R9|].
    split; [rewrite <- (getr_eqv _ _ XR); exact R18|].
    split.
    { unfold fmt_regs. rewrite <- !(getr_eqv _ _ XR).
      split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
    split; [|reflexivity].
    unfold rt_nk. rewrite len_zu. replace (length u - 1 + 1)%nat with (length u) by lia. reflexivity.
Qed.

Lemma st_p2_cf : PtK_cf at_p3 0x13390 -> PtK_cf at_p2 0x13364.
Proof.
  intros P3 f R mem1 md1 (L1 & A1 & res & FRM & BO & NE & KM & R10 & R9 & R19).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  assert (NL : (1 <= length u <= 255)%nat).
  { assert (length u <> 0)%nat by (intros H0; apply NE; apply length_zero_iff_nil; exact H0). lia. }
  eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_whole SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk).
    - exact R10.
    - exact R9.
    - exact NL.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13c1c) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x13390) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q9 : getr R2 9 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); exact R9).
  assert (Q18 : getr R2 18 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q19 : getr R2 19 = Z_to_bv 64 nz) by (rewrite <- (getr_eqv _ _ XR); exact R19).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 1) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold crt_glue.szb, crt_glue.nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold crt_glue.szb, crt_glue.nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_whole (ManifestMem.zbytes u)) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite len_whole, length_zb; unfold crt_glue.szb, crt_glue.nz; lia|].
  rewrite <- SEG.
  apply (names_glue_cf [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 1) bm
           (pf_bytes (txt_whole (ManifestMem.zbytes u))) (skipn (length (txt_whole (ManifestMem.zbytes u)) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. lia.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m_cf.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10' AW3 PK3 SL FK.
    rewrite Q1. apply (P3 fx2 regs2 mem3 md2).
    destruct (nm_cons NE (nm_pk peak) (cnt + 1)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|]. split; [exact NE|].
    split; [replace (cnt + 2) with (cnt + 1 + 1) by lia; exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK)|].
    split.
    { rewrite R10'. f_equal. rewrite zbytes_pf; [apply rt_whole; rewrite length_zb; lia|].
      pose proof (nz_whole _ (zbytes_nz u (proj1 (proj2 CU1)))) as Hn.
      rewrite Forall_forall in Hn |- *. intros c Hc. specialize (Hn c Hc). lia. }
    split; [transitivity (getr R2 9); [exact (RP 9 ltac:(unfold callee_saved; lia)) | exact Q9]|].
    split; [transitivity (getr R2 18); [exact (RP 18 ltac:(unfold callee_saved; lia)) | exact Q18]|].
    transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19].
Qed.

Lemma st_p1_cf : PtK_cf at_p2 0x13364 -> PtK_cf at_p1 0x13348.
Proof.
  intros P2. unfold PtK_cf in P2. intros f R mem1 md1 (L1 & A1 & FRM & KM & R10 & R19).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  destruct (Nat.eq_dec (length u) 0) as [E0|E0].
  - assert (EU : u = []) by (apply length_zero_iff_nil; exact E0).
    assert (NZ : nz = 0) by (unfold crt_glue.nz; rewrite E0; reflexivity).
    rewrite NZ in R19.
    assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ R) (frame_cells j (getr regs 8) (getr regs 9)
      (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
      (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 1))).
    { rewrite S1. apply rw_cells_normalize; [exact RA1 | exact FR |].
      intros x Hx. cbn [frame_cells cells_size csize] in Hx. right. lia. }
    eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_zero; [exact R10 | exact R19 | exact FRn |].
      change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    destruct (ka_post s _ _ _ _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
      as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
    set (mem2 := ms_mem s) in *.
    assert (Q2 : getr R2 2 = getr regs 2).
    { rewrite <- (getr_eqv _ _ XR).
      transitivity (Z_to_bv 64 (spZ R + 112)); [reflexivity|].
      rewrite S1. apply bv_eq. rewrite unsigned_lit by lia. unfold spZ. lia. }
    assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
    assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
    assert (RP0 : regs_preserved regs R2).
    { intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        first [exact Q2 | exact Q3 | exact Q4 | rewrite <- (getr_eqv _ _ XR); reflexivity]. }
    assert (IV2 : crt_inv B API CRT_K L A regs mem md [] L1 A1 mem2 md1).
    { eapply (inv_munch B API) with (W := []); first [exact SEG | exact AX | exact CTX | exact GS | exact IV
        | exact MU2 | exact WM2 | exact RA2 | rewrite crtk_val; lia | idtac].
      intros x Hx O. exfalso. apply O. exact I. }
    destruct (nm_nil EU peak cnt) as [EP EC].
    rewrite EP, EC in AW. rewrite EP in PK.
    rewrite (ret_pc_ok _ HRA). rewrite <- SEG. apply SRcf_ret. unfold crt_glue.QF, crt_post.
    eexists _, L1, A1, R2, mem2, md1.
    split; [reflexivity|].
    split; [exact FRM|].
    split; [exact INIT1|].
    split; [eapply (bpost_of_inv B API); first [exact SEG | exact IV2 | exact RP0]|].
    split; [destruct (u_cstr [] L1 A1 mem2 md1 IV2) as (us1 & CU1 & _); exists us1; exact CU1|].
    rewrite EU. cbn [ManifestMem.zbytes map rt_peak rt_calls].
    split; [|exact RES].
    rewrite Z.add_0_r.
    eapply ledger_rebuild; [exact SEG | exact IV2 | exact LG | | lia | lia | lia].
    apply (aw_munch B mem1 mem2 [] _ _ _ _ AW MU2). intros x _. exact I.
  - assert (NE : u <> []) by (intros E; apply E0; rewrite E; reflexivity).
    assert (NL : 1 <= nz <= 255) by (unfold crt_glue.nz; lia).
    eapply (ka_step_cf B); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_mal with (n := nz); [exact R10 | exact R19 | exact NL]. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    destruct (ka_post s _ _ _ _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
      as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
    set (mem2 := ms_mem s) in *.
    assert (Q1 : getr R2 1 = Z_to_bv 64 0x13364) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
    assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
    assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
    assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
    assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
    assert (Q9 : getr R2 9 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
    assert (Q10 : getr R2 10 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
    assert (Q19 : getr R2 19 = Z_to_bv 64 nz) by (rewrite <- (getr_eqv _ _ XR); exact R19).
    assert (KM2 : kmid [] L1 A1 R2 mem2 md1 (nm_pk peak) (nm_c cnt) b).
    { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 [] KM MU2 WM2 RA2); try assumption.
      intros x Hx O. exfalso. apply O. exact I. }
    pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
    destruct (nm_cons NE peak cnt) as [EP EC].
    assert (HR1 : room_ag b szb).
    { pose proof CAP0o as C1. pose proof BYUo as C2. pose proof cap_nn as C3.
      apply room_ag_of; [apply room_slots_small; unfold crt_glue.szb, crt_glue.nz in *; lia | lia
        | unfold crt_glue.szb, crt_glue.nz; lia]. }
    rewrite <- SEG.
    apply (malloc_glue_cf _ L1 A1 R2 mem2 md1 (nm_pk peak) (nm_c cnt) b szb).
    + exact IV2.
    + exact Q2.
    + rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
    + exact Q4.
    + exact Q10.
    + exact AW2.
    + exact RES2.
    + exact HR1.
    + intros L2 A2 regs2 mem3 md2 res IV3 RP R10' R16 FB AW3 SL FK.
      rewrite Q1. apply P2.
      exists L2, A2, res. split; [exact FRM|]. split; [exact (conj R16 FB)|]. split; [exact NE|].
      split.
      { rewrite EC in AW3.
        eapply e_kmid_call; [exact KM2 | exact IV3 | exact RP | exact AW3 | exact PK2 | exact SL | exact FK]. }
      split; [exact R10'|].
      split; [transitivity (getr R2 9); [exact (RP 9 ltac:(unfold callee_saved; lia)) | exact Q9]|].
      transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19].
Qed.

Lemma st_entry_cf : PtK_cf at_p1 0x13348 ->
  SRcf B (mkCfg (@mkst fx regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom (ms_segs B))) md) QF.
Proof.
  intros P1. unfold PtK_cf in P1.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof LG as (AW0 & PK0 & _).
  rewrite QF0 in AW0.
  destruct (mr_model _ _ (aa_laws API) L A mem md HM0) as (Hh & Hl & _).
  assert (IV0 : crt_inv B API CRT_K L A regs mem md [] L A mem md).
  { eapply (inv_init B API); first [exact SEG | exact PRE | exact INIT0 | exact RA0]. }
  pose proof IV0 as (_ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (u_cstr [] L A mem md IV0) as (us1 & CU1 & Lus1).
  destruct u_bounds as (UB1 & UB2).
  pose proof (ceil8_ge (bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1)) as Rus.
  assert (STK : stk rsegs (normalize_cj rsegs mem) (spZ regs - 8560) (spZ regs)).
  { apply stk_normalize; [|lia]. apply stk_of_writable; [lia | lia |].
    intros a Ha. apply HSC. left. rewrite crtk_val. lia. }
  eapply (ka_step_cf B); [exact SEG | exact RA0 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_pro STRL) with (lo := spZ regs - 8560) (u := u) (us := us1).
    - exact STK.
    - change (bv_unsigned (Sem.reg_get regs 2)) with (spZ regs). lia.
    - apply mem_inv_normalize.
    - assert (C8 : bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1 + Z.of_nat (length us1) <= alloc_ceiling).
      { rewrite Lus1. apply ceil8_le; [lia|]. destruct Hacv as [_ Hm]. Z.div_mod_to_equations. lia. }
      apply cstr_normalize; [exact RA0 | exact CU1 |]. try change (Sem.reg_get regs 10) with (getr regs 10). lia.
    - change (bv_unsigned (Sem.reg_get regs 2)) with (spZ regs).
      change (Sem.reg_get regs 10) with (getr regs 10). lia. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & m' &
    E & FR' & MU & WM & MI). subst s0.
  destruct (ka_post s _ _ _ _ _ ms' mem _ REL ROS EQV RA0 MU WM) as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x13348) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite <- (getr_eqv _ _ XR).
    change (bv_unsigned (Z_to_bv 64 (spZ regs + -112)) = spZ regs - 112).
    rewrite unsigned_lit by lia. lia. }
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q10 : getr R2 10 = Z_to_bv 64 0x102e7) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q19 : getr R2 19 = Z_to_bv 64 nz) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (MU3 : munch [(spZ regs - 112, spZ regs)] mem mem2) by exact MU2.
  assert (IV1 : crt_inv B API CRT_K L A regs mem md [] L A mem2 md).
  { eapply (inv_munch B API) with (W := [(spZ regs - 112, spZ regs)]); first [exact SEG | exact AX | exact CTX
      | exact GS | exact IV0 | exact MU3 | exact WM2 | exact RA2 | rewrite crtk_val; lia | idtac].
    intros x Hx O. left. rewrite crtk_val. cbn [outside] in O. lia. }
  assert (FR2 : rw_cells rsegs mem2 (spZ regs - 112) (fr junk)) by exact (rw_cells_rel mem2 m' _ _ MR2 FR').
  assert (AW1 : alloc_words B mem2 (lsum Lam) peak cnt (2 ^ 64 - 1)).
  { apply (aw_munch B mem mem2 [(spZ regs - 112, spZ regs)] _ _ _ _ AW0 MU3).
    intros x Hx. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. cbn [outside]. split; [lia | exact I]. }
  pose proof (crt_strings_keep mem mem2 RA0 RA2 CS0) as (CE & _).
  assert (UQ : bv_unsigned (getr R2 10) = 0x102e7) by (rewrite Q10; apply unsigned_lit; lia).
  rewrite <- SEG.
  apply (names_glue_cf [] _ L A R2 mem2 md peak cnt b [] []).
  - exact IV1.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM0.
  - exact Q11.
  - rewrite UQ. split; [exact CE|]. split; [constructor|]. apply Z.leb_le. reflexivity.
  - rewrite UQ. right. intros i Hi. cbn [length] in Hi. apply ro_first. lia.
  - rewrite UQ. lia.
  - cbn [length]. lia.
  - rewrite UQ. cbn [length]. lia.
  - rewrite UQ. unfold off_statics, G_LIVE, G_COUNT, G_FAIL. cbn [length]. lia.
  - exact AW1.
  - exact PK0.
  - exact QC0.
  - lia.
  - exact RES0.
  - exact room_b_cf.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10n AW3 PK3 SL FK.
    rewrite Q1. apply P1.
    exists L2, A2. split; [exact FRM2|].
    split.
    { split; [exact IV3|].
      split; [transitivity (spZ R2); [unfold spZ; f_equal; exact (RP 2 ltac:(unfold callee_saved; lia)) | exact Q2]|].
      split; [transitivity (getr R2 3); [exact (RP 3 ltac:(unfold callee_saved; lia)) | exact Q3]|].
      split; [transitivity (getr R2 4); [exact (RP 4 ltac:(unfold callee_saved; lia)) | exact Q4]|].
      split; [transitivity (getr R2 8); [exact (RP 8 ltac:(unfold callee_saved; lia)) | exact Q8]|].
      split; [exists junk; apply (rw_cells_keep mem2 mem3 _ _ FR2); intros a Ha;
              cbn [crt_glue.fr frame_cells cells_size csize] in Ha; apply FK; lia|].
      split; [exact AW3|]. split; [exact PK3 | exact SL]. }
    split; [rewrite R10n; f_equal; apply rt_empty|].
    transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19].
Qed.

Lemma crt_all_cf : SRcf B (mkCfg (@mkst fx regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom (ms_segs B))) md) QF.
Proof.
  pose proof st_exit_cf as EX.
  assert (T1 : forall k m, HeadK_cf (S k) (S m) -> PtK_cf (at_t 1 k m) 0x13430).
  { intros k m HK. exact (st_t1_cf k m (st_t2_cf k m (st_t3_cf k m (st_t4_cf EX k m HK)))). }
  pose proof (st_head_cf EX T1) as HD.
  exact (st_entry_cf (st_p1_cf (st_p2_cf (st_p3_cf (st_p4_cf EX (HD 1%nat 0%nat)))))).
Qed.

End G.
