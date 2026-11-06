(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: __interceptor_vfprintf of fm.asan (0x457ec, frame 0x30, entered from musl vsnprintf
   through __wrap_vfprintf) ported from A/AE35.v's walk: the entry state with the read-only image cells in vpA_rodata's
   form, TryAsanInitFromRtl and the common_flags ()->check_printf test run through, REAL (vfprintf) read from 0x9b740,
   the epilogue and ret as in tfib_vprintf_icpt_E; the inline printf_common run is replaced by a kcall of the
   printf_common contract (apcommon_realizesU), musl vfprintf by a kcall of avfp_realizes; the vprintf entry part
   (tfib_vprintf_icpt_A) is not used; stated as FMsnprintfGI's avfpi_realizes over FMsnprintfI's snk_frame. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvfi.v, with its module paths and module names changed; 297 of its 390 lines of code are new or changed and 314 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfSvfi.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 2 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfSvfi.table); YImgTop zify_pre_hook added after the last Require. *)
(* fm's __interceptor_vfprintf (fm.asan 0x46a7c, frame 0x30, entered from musl vsnprintf through __wrap_vfprintf)
   over the GXA-route form sh_avfprintf_icpt_realizesUx (FMsnprintfSx.v), generic in the format family and in the
   stack windows: TryAsanInitFromRtl and the common_flags ()->check_printf test run through, printf_common (ctx,
   format, aq) by its shared contract at a window Kp, REAL (vfprintf) read from 0xa3738 and musl vfprintf (the same
   FILE, format and ap) by the same Ux form at a window Kv, whose FP-existential post binds the FP state the epilogue
   then runs at; the interceptor's window is K. The same function as FMsnprintfGvfi.v's avfpi_ok, restated in the
   kit's vocabulary (FMsnprintfSk.v): the frame is sw_frame over the window [sp - K, sp) of the entry sp. Glue's runs
   are redone over a stack region of SVR = 64 bytes (the frame 0x30 and TryAsanInitFromRtl's 16 bytes below it) in
   place of Glue's VFI_K, so that K is free; the image cells and the shape checks are Glue's. New file. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMH_Base FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfSk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfGk0 FMsnprintfGt0 FMsnprintfGvfi0.
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the walk's symbolic states: atom 2 = the entry sp; the stack region is the 0x30-byte frame and the 16 bytes
   TryAsanInitFromRtl writes below it (MEASURED: Glue's v1_r0 holds chunks at -64 .. -8); the read-only image cells
   are Glue's vfi_rodata ---- *)
Definition SVR : Z := 64.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition svr_stk : YP09.region := YP09.mkRegion (Some 2%nat) (- SVR) 0 (- SVR) 0 [].
Definition svr_mem : smem := svr_stk :: map ro_region vfi_rodata.
Definition u0 : sstate := mkSS A_VFPI sr_atoms svr_mem None vfi_facts.
(* entry .. printf_common: prologue, TryAsanInitFromRtl, check_printf, aq *)
Definition u1_e : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_g FUEL A_PCOM u0).
Lemma r_u1 : sym_run_toN tfibsegs tbl_g FUEL A_PCOM u0 = (u1_e, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition u1_r0 : YP09.region := Eval vm_compute in hd svr_stk (ss_mem u1_e).
Definition u1_rest : smem := Eval vm_compute in tl (ss_mem u1_e).
(* printf_common's return .. REAL (vfprintf) *)
Definition u2_s : sstate := kafter 32 u1_e RA_PCOM_VFPI (-48) 0 0.
Definition u2_e : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_g FUEL A_VFP u2_s).
Lemma r_u2 : sym_run_toN tfibsegs tbl_g FUEL A_VFP u2_s = (u2_e, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition u2_r0 : YP09.region := Eval vm_compute in hd svr_stk (ss_mem u2_e).
Definition u2_rest : smem := Eval vm_compute in tl (ss_mem u2_e).
(* the image cells are dropped before musl vfprintf (the epilogue reads none) *)
Definition u3_c : sstate := set_mem u2_e [u2_r0].
(* vfprintf's return .. ret *)
Definition u3_s : sstate := kafter 48 u3_c RA_VFP (-48) 0 0.
Definition u3_e : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_g FUEL u3_s).
Lemma r_u3 : sym_runN tfibsegs tbl_g FUEL u3_s = (u3_e, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.

(* the shapes the proof reads off the states *)
Definition svr_winb (t : option nat * Z * Z) : bool :=
match t with
| (Some 2%nat, lo, hi) => (- SVR <=? lo) && (hi <=? 0)
| (_, lo, hi) => hi <=? lo
end.
Definition svr_win (rs : smem) : bool := forallb svr_winb (windows rs).
Definition svr_stk0 (rs : smem) : bool :=
match rs with
| r :: _ => match YP09.r_base r with Some 2%nat => (YP09.r_wlo r =? - SVR) && (YP09.r_whi r =? 0) | _ => false end
| [] => false
end.

Lemma u0_win : svr_win (ss_mem u0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u1_pc : ss_pc u1_e = A_PCOM. Proof. vm_compute. reflexivity. Qed.
Lemma u1_resv : ss_resv u1_e = None. Proof. vm_compute. reflexivity. Qed.
Lemma u1_ra : sr_get (ss_regs u1_e) 1 = SLit RA_PCOM_VFPI. Proof. vm_compute. reflexivity. Qed.
Lemma u1_sp : sr_get (ss_regs u1_e) 2 = SOff 2 (-48). Proof. vm_compute. reflexivity. Qed.
Lemma u1_r3 : sr_get (ss_regs u1_e) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma u1_r4 : sr_get (ss_regs u1_e) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma u1_r11 : sr_get (ss_regs u1_e) 11 = SOff 11 0. Proof. vm_compute. reflexivity. Qed.
Lemma u1_r12 : sr_get (ss_regs u1_e) 12 = SOff 12 0. Proof. vm_compute. reflexivity. Qed.
Lemma u1_mem : ss_mem u1_e = u1_r0 :: u1_rest. Proof. vm_compute. reflexivity. Qed.
Lemma u1_b : YP09.r_base u1_r0 = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma u1_lo : YP09.r_lo u1_r0 = - SVR. Proof. vm_compute. reflexivity. Qed.
Lemma u1_hi : YP09.r_hi u1_r0 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma u1_wlo : YP09.r_wlo u1_r0 = - SVR. Proof. vm_compute. reflexivity. Qed.
Lemma u1_whi : YP09.r_whi u1_r0 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma u1_at : ss_atoms_lt 32 u1_e = true. Proof. vm_compute. reflexivity. Qed.
Lemma u1_wf : regions_wf (ss_mem (kafter 32 u1_e RA_PCOM_VFPI (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u1_nc : no_cdata (ss_mem (kafter 32 u1_e RA_PCOM_VFPI (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u1_ma : mem_atoms_lt 32 (ss_mem (kafter 32 u1_e RA_PCOM_VFPI (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u1_ci : forallb (chunk_inside u1_r0) (YP09.r_chunks u1_r0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u1_far : forallb ro_far u1_rest = true. Proof. vm_compute. reflexivity. Qed.
Lemma u1_stk : svr_stk0 (ss_mem u1_e) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u2_win : svr_win (ss_mem u2_s) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u2_stk : svr_stk0 (ss_mem u2_e) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u2_mem : ss_mem u2_e = u2_r0 :: u2_rest. Proof. vm_compute. reflexivity. Qed.
Lemma u2_b : YP09.r_base u2_r0 = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma u2_lo : YP09.r_lo u2_r0 = - SVR. Proof. vm_compute. reflexivity. Qed.
Lemma u2_hi : YP09.r_hi u2_r0 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma u2_wlo : YP09.r_wlo u2_r0 = - SVR. Proof. vm_compute. reflexivity. Qed.
Lemma u2_whi : YP09.r_whi u2_r0 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_pc : ss_pc u3_c = A_VFP. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_resv : ss_resv u3_c = None. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_mem : ss_mem u3_c = [u2_r0]. Proof. reflexivity. Qed.
Lemma u3c_ra : sr_get (ss_regs u3_c) 1 = SLit RA_VFP. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_sp : sr_get (ss_regs u3_c) 2 = SOff 2 (-48). Proof. vm_compute. reflexivity. Qed.
Lemma u3c_r3 : sr_get (ss_regs u3_c) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_r4 : sr_get (ss_regs u3_c) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_r10 : sr_get (ss_regs u3_c) 10 = SOff 10 0. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_r11 : sr_get (ss_regs u3_c) 11 = SOff 11 0. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_r12 : sr_get (ss_regs u3_c) 12 = SOff 12 0. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_at : ss_atoms_lt 48 u3_c = true. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_wf : regions_wf (ss_mem (kafter 48 u3_c RA_VFP (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_nc : no_cdata (ss_mem (kafter 48 u3_c RA_VFP (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_ma : mem_atoms_lt 48 (ss_mem (kafter 48 u3_c RA_VFP (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u3c_ci : forallb (chunk_inside u2_r0) (YP09.r_chunks u2_r0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u3s_win : svr_win (ss_mem u3_s) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u3e_stk : svr_stk0 (ss_mem u3_e) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u3e_resv : ss_resv u3_e = None. Proof. vm_compute. reflexivity. Qed.
Lemma u3e_ret : clookup tbl_g (ss_pc u3_e) = Some RET_WORD_r. Proof. vm_compute. reflexivity. Qed.
Lemma u3e_ra : sr_get (ss_regs u3_e) 1 = SOff 1 0. Proof. vm_compute. reflexivity. Qed.
Lemma u3e_r10 : sr_get (ss_regs u3_e) 10 = SOff 52 0. Proof. vm_compute. reflexivity. Qed.
Lemma u3e_kept : regs_kept u3_e = true. Proof. vm_compute. reflexivity. Qed.
End r.

(* the cells musl vfprintf may write outside its stack band: the written destination, the FILE, the cookie *)
Definition svfi_xw (s0 w fp cp a : Z) : Prop := (s0 <= a < s0 + w) \/ (fp <= a < fp + 232) \/ (cp <= a < cp + 16).
Lemma Exists_zr3 : forall a r1 r2 r3, Exists (in_zr a) [r1; r2; r3] -> in_zr a r1 \/ in_zr a r2 \/ in_zr a r3.
Proof. intros a r1 r2 r3 HE. rewrite !Exists_cons, Exists_nil in HE. tauto. Qed.

(* ---- general lemmas of the walk (Glue's vfi_win_sound / vfi_present over SVR) ---- *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma svr_win_sound : forall E rs a, svr_win rs = true -> in_wrange E rs a ->
  bv_unsigned (ew E 2) - SVR <= a < bv_unsigned (ew E 2).
Proof.
intros E rs a Hw Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr).
unfold svr_win in Hw. rewrite forallb_forall in Hw. specialize (Hw _ Ht). unfold svr_winb in Hw.
destruct b as [[|[|[|n]]]|]; cbn [base_val] in Hr; cbn in Hw; try (apply Z.leb_le in Hw; lia).
apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold SVR in *. lia.
Qed.
Lemma svr_present : forall (Hd : word -> bool) E rs ss1 ms1 (m : word -> option byte) a,
  svr_win rs = true -> svr_stk0 (ss_mem ss1) = true -> TFIB_IMG_END <= bv_unsigned (ew E 2) - SVR ->
  frame_of E rs m (ms_mem ms1) -> st_ok tfibsegs E ss1 (restrict Hd ms1) ->
  0 <= a < 2 ^ 64 -> apresent Hd m a -> apresent Hd (ms_mem ms1) a.
Proof.
intros Hd E rs ss1 ms1 m a Hw Hs Hlo HF HS Ha Hp.
destruct (ss_mem ss1) as [|r1 rest] eqn:Hm; [discriminate|].
unfold svr_stk0 in Hs. destruct (YP09.r_base r1) as [[|[|[|n]]]|] eqn:Hb; cbn in Hs; try discriminate.
apply andb_prop in Hs as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
assert (OUT : ~ (bv_unsigned (ew E 2) - SVR <= a < bv_unsigned (ew E 2)) -> apresent Hd (ms_mem ms1) a).
{ intros Hn. apply (apresent_same Hd m); [|exact Hp]. apply HF. rewrite unsigned_lit_small by lia.
  intros Hin. exact (Hn (svr_win_sound E rs a Hw Hin)). }
destruct (Z_lt_le_dec a (bv_unsigned (ew E 2) - SVR)) as [L|L]; [apply OUT; lia|].
destruct (Z_lt_le_dec a (bv_unsigned (ew E 2))) as [L2|L2]; [|apply OUT; lia].
apply (st_ok_window_apresent Hd E ss1 ms1 0 r1 a HS); [rewrite Hm; reflexivity | rewrite Hb, H1, H2; cbn [base_val]; lia | lia].
Qed.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
(* a run of the walk's own code keeps the frame over a window [sp - K, sp) that holds the stack region *)
Lemma svfi_run : forall ly S U W mem0 md0 XW XP K sp mem md E ss ss1 ms1 mat,
  ly_stk_lo ly <= sp - K -> sp <= ly_stk_hi ly -> SVR <= K -> TFIB_IMG_END <= sp - K -> sp <= 2 ^ 63 ->
  sw_frame B ly S U W mem0 md0 (sp - K) sp XW XP mem md ->
  svr_win (ss_mem ss) = true -> svr_stk0 (ss_mem ss1) = true -> bv_unsigned (ew E 2) = sp ->
  frame_of E (ss_mem ss) mem (ms_mem ms1) -> st_ok tfibsegs E ss1 (restrict (w_H W) ms1) ->
  sw_frame B ly S U W mem0 md0 (sp - K) sp XW XP (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S U W mem0 md0 XW XP K sp mem md E ss ss1 ms1 mat Hl Hh HK Hi H63 HF Hw Hs H2 HFo HS.
assert (HIE : TFIB_IMG_END = 6635520) by reflexivity.
pose proof HF as (_ & _ & Hp & _ & _).
apply (sw_run B LAWS ly S U W mem0 md0 (sp - K) sp XW XP Hl Hh mem md (ms_mem ms1) mat E (ss_mem ss) HF).
- intros a Ha. pose proof (svr_win_sound E _ a Hw Ha) as X. rewrite H2 in X. lia.
- exact HFo.
- intros a Ha. apply (svr_present (w_H W) E (ss_mem ss) ss1 ms1 mem a Hw Hs); [rewrite H2; lia | exact HFo | exact HS | lia |].
  exact (Hp a Ha).
Qed.
End h.

(* ---- the contract ---- *)
Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.
(* Kp: printf_common's window, Kv: musl vfprintf's window, both below the frame 0x30; K: the interceptor's window *)
Theorem svfi_ok : forall FF gc gv img_lo img_hi cr Kp Kv K, ff_stable64 FF -> ff_mono FF ->
  ESTACK <= Kv -> 0x30 + Kv <= K -> 0x30 + Kp <= K ->
  sh_apcommon_realizesUz tfibsegs B FF Kp cr A_PCOM ->
  sh_avfprintf_icpt_realizesUx tfibsegs B FF Kv gc gv img_lo img_hi cr A_SNW A_VFP ->
  sh_avfprintf_icpt_realizesUx tfibsegs B FF K gc gv img_lo img_hi cr A_SNW A_VFPI.
Proof.
intros FF gc gv img_lo img_hi cr Kp Kv K STAB MONO HKv HKK HKP APCOMMON AVFP.
assert (HES : ESTACK = 4096) by reflexivity.
apply (vf_contractX B FF K gc gv img_lo img_hi cr A_SNW A_VFPI); [lia|].
intros ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HPRE Hdog Hfrm Hnul Ho1 Ho2 Ho3 Hdsj H47 Hd8 Hra G3 G4 G10 G11 G12.
pose proof HPRE as (HA & Hlo & Hhi & H16 & HK & Hp & Hfile & Hbp & Hck & Hdf & Hdc & XF1 & XF2 & XC1 & XC2 & Hcv & Hcb &
  Hcd & Hgc & Hgv & XG1 & XG2 & XG3 & XG4 & Hgcd & Hgvd & Hws & XA1 & XA2 & Ad & HFF & Hn0 & HT & Hs0 & Hsw & Hpw & Hdst &
  Ham & Hra' & Hhull).
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
assert (HSVR : SVR = 64) by reflexivity. assert (HIE : TFIB_IMG_END = 6635520) by reflexivity.
assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity. assert (KHE : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (sn_len_pos n0 T) as Hw1.
pose proof Hpw as Hpw'. unfold vf_rs in Hpw'. apply pairwise_vfp in Hpw' as (P1 & P2 & P3 & _).
unfold zdisjoint in P1, P2, P3. cbn [fst snd] in P1, P2, P3.
assert (H16' : (spZ regs - 48) mod 16 = 0).
{ rewrite <- (Z_mod_plus_full (spZ regs - 48) 3 16). replace (spZ regs - 48 + 3 * 16) with (spZ regs) by lia. exact H16. }
assert (HLO : ly_stk_lo ly <= spZ regs - K) by lia.
assert (HIM : TFIB_IMG_END <= spZ regs - K) by lia.
assert (HSK : SVR <= K) by lia.
assert (H63 : spZ regs <= 2 ^ 63) by lia.
assert (EEr : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Ereg regs []) i = getr regs r)
  by (intros i r Hi; exact (ew_Ereg_nat regs [] i r Hi)).
assert (EE2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (EEr 2%nat 2%bv eq_refl); reflexivity).
(* the entry state *)
assert (HS0 : st_ok tfibsegs (Ereg regs []) u0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_VFPI) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold u0. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
    + unfold svr_stk. apply (region_ok_stack tfibsegs (Ereg regs []) _ 2 (spZ regs) (- SVR)); [exact EE2 | lia | lia |].
      intros a Ha. apply apresent_writable. apply Hp. lia.
    + apply (vfi_ro_region_low vfi_rodata (Ereg regs []) (mrestrict (w_H W) (unpoison U mem))); [vm_compute; reflexivity | |].
      * intros w Hw. unfold mrestrict. rewrite (ARU_mem_low tfibsegs B ly S U W mem md w HA Hw). reflexivity.
      * exact (rodata_ok B TB vfi_rodata ly S (w_H W) (unpoison U mem) (Ereg regs []) (vfi_rodata_chk ly)
          (ARU_ARm tfibsegs B ly S U W mem md HA)).
  - apply pairwise_disjoint_of_extents. unfold svr_mem, svr_stk, vfi_rodata, icpt_rodata, ro_region, extent_of_region.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. unfold vfi_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite EE2. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [exact H16 | lia]. }
pose proof (sw_init B ly S U W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) HA Hp) as F0.
unfold cfg_at, w64.
(* run 1: entry .. printf_common *)
eapply SRr_bind; [exact (g_phase_to W (Ereg regs []) A_PCOM u0 u1_e RS_running _ md HS0 r_u1)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
assert (HS1' : st_ok tfibsegs (Ereg regs []) u1_e (restrict (w_H W) ms1)) by exact HS1. clear HS1.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
pose proof (svfi_run B LAWS ly S U W mem md (fun _ => False) (fun _ => False) K (spZ regs) mem md (Ereg regs []) u0
  u1_e ms1 mat1
  HLO Hhi HSK HIM H63 F0 u0_win u1_stk EE2 HF1 HS1') as F1. fold md1 in F1.
pose proof F1 as (F1a & _ & F1p & F1f & F1m).
assert (PRE1 : vf_pre B FF K gc gv cr A_SNW ly S U W (ms_mem ms1) md1 (spZ regs) fp f ap bp cp s0 n0 ws T cval).
{ apply (vf_pre_keep B FF K gc gv cr A_SNW ly S U W mem md (ms_mem ms1) md1 (spZ regs) fp f ap bp cp s0 n0 ws T cval
    STAB HPRE F1a F1p); [|exact (apresent_kept64 (w_H W) mem (ms_mem ms1) (fun a Ha Hpa => F1m a Ha Hpa (fun X => X)))].
  intros a Ha Hn. apply F1f; [exact Ha | exact Hn | exact (fun X => X)]. }
assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 RA_PCOM_VFPI) by exact (g_reg W _ u1_e ms1 1 _ HS1' u1_ra).
assert (RA1 : raZ (ms_regs ms1) = RA_PCOM_VFPI) by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold RA_PCOM_VFPI; lia).
assert (Sp1 : spZ (ms_regs ms1) = spZ regs - 48).
{ unfold spZ at 1. rewrite (g_reg W _ u1_e ms1 2 _ HS1' u1_sp). cbn [sv_denot]. rewrite EE2.
  rewrite unsigned_lit_small by lia. lia. }
assert (R13 : getr (ms_regs ms1) 3 = w64 (as_gp B))
  by (rewrite (g_reg W _ u1_e ms1 3 _ HS1' u1_r3), (sv_atom _ 3 regs 3 (EEr 3%nat 3%bv eq_refl)); exact G3).
assert (R14 : getr (ms_regs ms1) 4 = w64 (as_tp B))
  by (rewrite (g_reg W _ u1_e ms1 4 _ HS1' u1_r4), (sv_atom _ 4 regs 4 (EEr 4%nat 4%bv eq_refl)); exact G4).
assert (R111 : getr (ms_regs ms1) 11 = w64 f)
  by (rewrite (g_reg W _ u1_e ms1 11 _ HS1' u1_r11), (sv_atom _ 11 regs 11 (EEr 11%nat 11%bv eq_refl)); exact G11).
assert (R112 : getr (ms_regs ms1) 12 = w64 ap)
  by (rewrite (g_reg W _ u1_e ms1 12 _ HS1' u1_r12), (sv_atom _ 12 regs 12 (EEr 12%nat 12%bv eq_refl)); exact G12).
pose proof (vf_pcom B FF K Kp gc gv cr A_SNW ly S U W (ms_mem ms1) md1 (spZ regs) (spZ (ms_regs ms1))
  fp f ap bp cp s0 n0 ws T cval MONO PRE1 ltac:(lia) ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
(* call printf_common (ctx, fmt, aq) at sp - 0x30: the region's 16 bytes below the frame are the band, the rest of
   its window [sp - 0x30 - Kp, sp - SVR) is XW *)
eapply SRr_bind.
{ apply (kcall W (Ereg regs []) u1_e ms1 md1 (spZ regs) SVR u1_r0 u1_rest 32 RA_PCOM_VFPI (-48) 0 0 16
    (fun a => spZ regs - 48 - Kp <= a < spZ regs - SVR) (fun regs2 mem2 md2 => ARU tfibsegs B ly S U W mem2 md2)
    HS1' u1_resv EE2 u1_mem u1_b u1_lo u1_hi ltac:(rewrite u1_wlo; lia) ltac:(rewrite u1_whi; lia) u1_ra u1_sp
    u1_at u1_wf u1_nc u1_ma u1_ci);
    first [ lia
          | solve [intros a Hx Ha; cbv beta in Hx; lia]
          | solve [intros r a Hr Ha; destruct (ro_far_sound (Ereg regs []) _ r a u1_far Hr) as [X _]; specialize (X Ha);
                   cbv beta; lia]
          | solve [intros r a Hr Ha; exfalso; destruct (ro_far_sound (Ereg regs []) _ r a u1_far Hr) as [_ X]; exact (X Ha)]
          | solve [intros a Ha; apply F1p; lia]
          | idtac ].
  rewrite u1_pc. eapply SRr_mono.
  { apply (APCOMMON ly S U W (ms_regs ms1) (ms_mem ms1) md1 f ap ws T);
      first [ assumption | lia | solve [intros a Ha; apply F1p; lia] | idtac ].
    apply (g_ecall_preU B ly S U W (ms_regs ms1) (ms_mem ms1) md1 F1a);
      first [ assumption | lia | solve [intros a Ha; apply F1p; lia] | solve [rewrite Sp1; exact H16']
            | solve [rewrite R1; apply ret_ok_lit; [unfold RA_PCOM_VFPI; lia | reflexivity]] ]. }
  cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HA2 & HP2' & Hsb2 & Hfr2 & Hpm2).
  split; [reflexivity|]. exists regs2, mem2, md2. rewrite RA1.
  split; [reflexivity|]. split; [exact HP2'|]. split; [exact Hsb2|].
  split; [intros a Ha Hn Hx; cbv beta in Hx; apply Hfr2; [exact Ha | rewrite Sp1; lia]|].
  split; [exact Hpm2 | exact HA2]. }
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & _ & Hfr2 & Hpm2 & HA2).
set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *.
set (E2 := havoc (Ereg regs []) 32 (map (getr (ms_regs ms2)) CLOB)) in HS2.
assert (E2r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> (i < 32)%nat -> ew E2 i = getr regs r).
{ intros i r Hi Hl. subst E2. rewrite ew_havoc_old by lia. exact (EEr i r Hi). }
assert (E22 : bv_unsigned (ew E2 2) = spZ regs) by (subst E2; rewrite ew_havoc_old by lia; exact EE2).
assert (F2 : sw_frame B ly S U W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) (ms_mem ms2) md2).
{ apply (sw_step B ly S U W mem md _ _ _ _ (ms_mem ms1) md1 _ _ F1 HA2).
  - apply with_vm_backing_same.
  - intros a Ha. apply Hpm2. apply F1p. exact Ha.
  - intros a Ha Hn _. apply Hfr2; [exact Ha | lia | cbv beta; lia].
  - intros a _ Hpa _. exact (Hpm2 a Hpa). }
(* run 2: printf_common's return .. REAL (vfprintf) *)
eapply SRr_bind; [exact (g_phase_to W E2 A_VFP u2_s u2_e RS_running ms2 md2 HS2 r_u2)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
assert (HS3' : st_ok tfibsegs E2 u2_e (restrict (w_H W) ms3)) by exact HS3. clear HS3.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2).
pose proof (svfi_run B LAWS ly S U W mem md (fun _ => False) (fun _ => False) K (spZ regs) (ms_mem ms2) md2 E2 u2_s
  u2_e ms3 mat3
  HLO Hhi HSK HIM H63 F2 u2_win u2_stk E22 HF3 HS3') as F3. fold md3 in F3.
pose proof F3 as (F3a & _ & F3p & F3f & F3m).
assert (PRE3 : vf_pre B FF K gc gv cr A_SNW ly S U W (ms_mem ms3) md3 (spZ regs) fp f ap bp cp s0 n0 ws T cval).
{ apply (vf_pre_keep B FF K gc gv cr A_SNW ly S U W mem md (ms_mem ms3) md3 (spZ regs) fp f ap bp cp s0 n0 ws T cval
    STAB HPRE F3a F3p); [|exact (apresent_kept64 (w_H W) mem (ms_mem ms3) (fun a Ha Hpa => F3m a Ha Hpa (fun X => X)))].
  intros a Ha Hn. apply F3f; [exact Ha | exact Hn | exact (fun X => X)]. }
pose proof (st_ok_first E2 u2_e _ u2_r0 u2_rest HS3' u2_mem) as HS3c. fold u3_c in HS3c.
assert (R31 : getr (ms_regs ms3) 1 = Z_to_bv 64 RA_VFP) by exact (g_reg W _ u3_c ms3 1 _ HS3c u3c_ra).
assert (RA3 : raZ (ms_regs ms3) = RA_VFP) by (unfold raZ; rewrite R31; apply unsigned_lit_small; unfold RA_VFP; lia).
assert (Sp3 : spZ (ms_regs ms3) = spZ regs - 48).
{ unfold spZ at 1. rewrite (g_reg W _ u3_c ms3 2 _ HS3c u3c_sp). cbn [sv_denot]. rewrite E22.
  rewrite unsigned_lit_small by lia. lia. }
assert (R33 : getr (ms_regs ms3) 3 = w64 (as_gp B))
  by (rewrite (g_reg W _ u3_c ms3 3 _ HS3c u3c_r3), (sv_atom _ 3 regs 3 (E2r 3%nat 3%bv eq_refl ltac:(lia))); exact G3).
assert (R34 : getr (ms_regs ms3) 4 = w64 (as_tp B))
  by (rewrite (g_reg W _ u3_c ms3 4 _ HS3c u3c_r4), (sv_atom _ 4 regs 4 (E2r 4%nat 4%bv eq_refl ltac:(lia))); exact G4).
assert (R310 : getr (ms_regs ms3) 10 = w64 fp)
  by (rewrite (g_reg W _ u3_c ms3 10 _ HS3c u3c_r10), (sv_atom _ 10 regs 10 (E2r 10%nat 10%bv eq_refl ltac:(lia))); exact G10).
assert (R311 : getr (ms_regs ms3) 11 = w64 f)
  by (rewrite (g_reg W _ u3_c ms3 11 _ HS3c u3c_r11), (sv_atom _ 11 regs 11 (E2r 11%nat 11%bv eq_refl ltac:(lia))); exact G11).
assert (R312 : getr (ms_regs ms3) 12 = w64 ap)
  by (rewrite (g_reg W _ u3_c ms3 12 _ HS3c u3c_r12), (sv_atom _ 12 regs 12 (E2r 12%nat 12%bv eq_refl ltac:(lia))); exact G12).
assert (Hret3 : YK0s.ret_ok (getr (ms_regs ms3) 1)) by (rewrite R31; apply ret_ok_lit; [unfold RA_VFP; lia | reflexivity]).
(* musl vfprintf's premises at its window [sp - 0x30 - Kv, sp - 0x30) *)
assert (PRE3s : vf_pre B FF Kv gc gv cr A_SNW ly S U W (ms_mem ms3) md3 (spZ (ms_regs ms3)) fp f ap bp cp s0 n0 ws T
  cval).
{ apply (vf_pre_shrink B FF K Kv gc gv cr A_SNW ly S U W (ms_mem ms3) md3 (spZ regs) (spZ (ms_regs ms3))
    fp f ap bp cp s0 n0 ws T cval MONO PRE3); [lia | lia | lia | rewrite Sp3; exact H16']. }
(* call musl vfprintf (f, fmt, ap) at sp - 0x30: it returns at an FP state fx'. Nothing before it touched the FP
   state, so the walk's frm0_entry is its own; the NUL at s0 is kept (s0 is outside the window); the FILE, the cookie
   and the arguments lie above sp >= sp - 0x30; the destination below the walk's window lies below the callee's *)
assert (Hnul3 : aview tfibsegs (w_H W) (ms_mem ms3) s0 = Some 0).
{ rewrite F3f; [exact Hnul | lia | lia | exact (fun X => X)]. }
assert (Ho1' : spZ (ms_regs ms3) <= fp) by lia.
assert (Hdsj' : s0 + sn_len n0 T <= spZ (ms_regs ms3) - Kv \/ ap + 8 * Z.of_nat (length ws) <= s0)
  by (destruct Hdsj as [X|X]; [left; lia | right; exact X]).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ _ HS3c u3c_resv) as Hshape3.
rewrite Hshape3, u3c_pc.
apply (srr_fx_continue tfibsegs W _ (raZ (ms_regs ms3))
  (fun fx' regs' mem' md' => ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved (ms_regs ms3) regs' /\
     same_but_materialized md3 md' /\ getr regs' 10 = w64 (Z.of_nat (length T)) /\
     (forall i, 0 <= i < sn_len n0 T ->
        aview tfibsegs (w_H W) mem' (s0 + i) = Some (nth (Z.to_nat i) (sn_bytes n0 T) 0)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (s0 <= a < s0 + sn_len n0 T) ->
        ~ Exists (in_zr a) [(spZ (ms_regs ms3) - Kv, Kv); (fp, 232); (cp, 16)] ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms3) a) /\
     (forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) (ms_mem ms3) a ->
        ~ (s0 <= a < s0 + sn_len n0 T /\ in_img tfibsegs a) -> apresent (w_H W) mem' a))).
{ exact (vf_applyX B FF Kv gc gv img_lo img_hi cr A_SNW A_VFP ly S U W (ms_regs ms3) (ms_mem ms3) md3
    fp f ap bp cp s0 n0 ws T cval AVFP PRE3s Hdog Hfrm Hnul3 Ho1' Ho2 Ho3 Hdsj' H47 Hd8 Hret3 R33 R34 R310 R311 R312). }
intros fx' regs4 mem4 md4 Hf1 Hf2 (HA4 & HP4 & Hsb4 & H10 & HDb & Hfr4 & Hpm4).
rewrite RA3.
(* what musl vfprintf changed: the region's 16 bytes below the frame (the band), the rest of its window, the
   destination, the FILE, the cookie *)
assert (FR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -48 - 16 <= a < spZ regs + -48) ->
  ~ ((spZ regs - 48 - Kv <= a < spZ regs - SVR) \/ svfi_xw s0 (sn_len n0 T) fp cp a) ->
  aview tfibsegs (w_H W) mem4 a = aview tfibsegs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn Hx. unfold svfi_xw in Hx. apply Hfr4; [exact Ha | intros X; apply Hx; right; left; exact X |].
  intros HE. apply Exists_zr3 in HE. unfold in_zr in HE. cbn [fst snd] in HE. rewrite Sp3 in HE. lia. }
assert (XPW : forall a, s0 <= a < s0 + sn_len n0 T /\ in_img tfibsegs a -> ~ (spZ regs - K <= a < spZ regs))
  by (intros a [X _] Ha; clear - X Ha P1; lia).
set (E4 := havoc E2 48 (map (getr regs4) CLOB)).
(* the state after the call, at fx' *)
assert (HS4 : st_ok (fx:=fx') tfibsegs E4 (kafter 48 u3_c RA_VFP (-48) 0 0)
  (restrict (w_H W) (mkst (fx:=fx') regs4 (Z_to_bv 64 RA_VFP) mem4 (seg_rom tfibsegs)))).
{ apply (kcall_fx fx fx' W E2 u3_c ms3 (spZ regs) SVR u2_r0 [] 48 RA_VFP (-48) 0 0 16
    (fun a => (spZ regs - 48 - Kv <= a < spZ regs - SVR) \/ svfi_xw s0 (sn_len n0 T) fp cp a)
    (fun a => s0 <= a < s0 + sn_len n0 T /\ in_img tfibsegs a) regs4 mem4
    HS3c u3c_resv E22 u3c_mem u2_b u2_lo u2_hi ltac:(rewrite u2_wlo; lia) ltac:(rewrite u2_whi; lia)
    u3c_at u3c_wf u3c_nc u3c_ma u3c_ci);
    first [ exact Hpm4
          | solve [intros a Hx Ha; apply (XPW a Hx); clear - Ha HSK; lia]
          | lia
          | solve [intros a Hx Ha; exfalso; cbv beta in Hx; unfold svfi_xw in Hx; lia]
          | solve [intros r a Hr; destruct Hr]
          | solve [intros a Ha; apply F3p; lia]
          | exact HP4 | exact FR4 ]. }
assert (E4r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> (i < 32)%nat -> ew E4 i = getr regs r).
{ intros i r Hi Hl. subst E4. rewrite ew_havoc_old by lia. exact (E2r i r Hi Hl). }
assert (E42 : bv_unsigned (ew E4 2) = spZ regs) by (subst E4; rewrite ew_havoc_old by lia; exact E22).
assert (F4 : sw_frame B ly S U W mem md (spZ regs - K) (spZ regs) (svfi_xw s0 (sn_len n0 T) fp cp)
  (fun a => s0 <= a < s0 + sn_len n0 T /\ in_img tfibsegs a) mem4 md4).
{ apply (sw_step B ly S U W mem md _ _ _ _ (ms_mem ms3) md3 mem4 md4
    (sw_mono B ly S U W mem md _ _ (fun _ => False) (fun _ => False) _ _ _ _ F3 (fun a X => match X with end)
       (fun a X => match X with end)) HA4 Hsb4).
  - intros a Ha. apply Hpm4; [clear - Ha HLO K1 KHB Hhi K2 KHE; lia | apply F3p; exact Ha | intros X; exact (XPW a X Ha)].
  - intros a Ha Hn Hx. apply FR4; [exact Ha | lia | intros [X|X]; [lia | exact (Hx X)]].
  - exact Hpm4. }
(* run 3: vfprintf's return .. ret, at fx' *)
unfold cfg_at, w64.
eapply SRr_bind; [exact (g_phase W E4 u3_s u3_e (RS_stopped (SR_jalr (SOff 1 0))) _ md4 HS4 r_u3)|].
intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5).
assert (HS5' : st_ok (fx:=fx') tfibsegs E4 u3_e (restrict (w_H W) ms5)) by exact HS5. clear HS5.
apply (g_ret W E4 u3_e ms5 (with_vm_backing (m_vm_lazy md4) mat5 md4) _ HS5' u3e_resv u3e_ret).
intros mat'. rewrite (wvb_collapse (m_vm_lazy md4) mat' mat5 md4).
pose proof (svfi_run B LAWS ly S U W mem md (svfi_xw s0 (sn_len n0 T) fp cp)
  (fun a => s0 <= a < s0 + sn_len n0 T /\ in_img tfibsegs a) K (spZ regs) mem4 md4 E4 u3_s u3_e ms5 mat'
  HLO Hhi HSK HIM H63 F4 u3s_win u3e_stk E42 HF5 HS5') as F5.
pose proof F5 as (F5a & F5s & _ & F5f & F5m).
assert (R51 : getr (ms_regs ms5) 1 = getr regs 1)
  by (rewrite (g_reg W _ u3_e ms5 1 _ HS5' u3e_ra); exact (sv_atom _ 1 regs 1 (E4r 1%nat 1%bv eq_refl ltac:(lia)))).
assert (R510 : getr (ms_regs ms5) 10 = w64 (Z.of_nat (length T))).
{ rewrite (g_reg W _ u3_e ms5 10 _ HS5' u3e_r10). cbn [sv_denot].
  pose proof (ew_havoc_new E2 48 (map (getr regs4) CLOB) 4 (Z_to_bv 64 0) ltac:(unfold CLOB; cbn [map length]; lia)) as X.
  cbn [Nat.add] in X. fold E4 in X. rewrite X. unfold CLOB. cbn [map nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  exact H10. }
unfold vf_post. split; [reflexivity|].
exists fx', (ms_regs ms5), (ms_mem ms5), (with_vm_backing (m_vm_lazy md4) mat' md4).
split.
{ unfold cfg_at. rewrite R51. unfold YK0s.ret_ok in Hra. rewrite Hra. unfold w64, raZ. rewrite Z_to_bv_bv_unsigned.
  reflexivity. }
split; [exact Hf1|]. split; [exact Hf2|]. split; [exact F5a|].
split; [exact (vfi_preserved (w_H W) E4 u3_e ms5 regs HS5' u3e_kept E4r)|].
split; [exact F5s|]. split; [exact R510|].
split.
{ intros i Hi. rewrite (aview_same (w_H W) mem4 (ms_mem ms5) (s0 + i)); [exact (HDb i Hi)|].
  apply HF5. rewrite unsigned_lit_small by lia. intros Hw.
  pose proof (svr_win_sound E4 _ _ u3s_win Hw) as X. rewrite E42 in X. lia. }
split; [|exact F5m].
intros a Ha Hs Hn. apply F5f; [exact Ha | |].
- intros X. apply Hn. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- unfold svfi_xw. intros [X|[X|X]]; [exact (Hs X) | |]; apply Hn;
    [apply Exists_cons_tl, Exists_cons_hd | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd];
    unfold in_zr; cbn [fst snd]; lia.
Qed.
End v.
