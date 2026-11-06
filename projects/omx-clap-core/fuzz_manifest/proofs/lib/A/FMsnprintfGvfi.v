(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: __interceptor_vfprintf of fm.asan (0x457ec, frame 0x30, entered from musl vsnprintf
   through __wrap_vfprintf) ported from A/AE35.v's walk: the entry state with the read-only image cells in vpA_rodata's
   form, TryAsanInitFromRtl and the common_flags ()->check_printf test run through, REAL (vfprintf) read from 0x9b740,
   the epilogue and ret as in tfib_vprintf_icpt_E; the inline printf_common run is replaced by a kcall of the
   printf_common contract (apcommon_realizesU), musl vfprintf by a kcall of avfp_realizes; the vprintf entry part
   (tfib_vprintf_icpt_A) is not used; stated as FMsnprintfGI's avfpi_realizes over FMsnprintfI's snk_frame. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMsnprintfI FMsnprintfK.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMsnprintfGI FMsnprintfGk FMsnprintfGt.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the walk's symbolic states: atom 2 = the entry sp = sp0 + 0x30; the stack region covers the callees' bands
   below it (musl vfprintf's SNK_STK below sp0); the read-only image cells are icpt_rodata (TryAsanInitFromRtl's
   asan_inited) and the common_flags pointer, check_printf and REAL (vfprintf) ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition vfi_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0x999a0, 8, [(0, 8%N, 0x1338a8)]); (0x1338fc, 1, [(0, 1%N, 1)]); (0x9b740, 8, [(0, 8%N, 0x8ede0)])].
Lemma vfi_rodata_chk : forall ly, rodata_chk ly vfi_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition VFI_K : Z := 9152. (* SNK_STK + OSP_VFPI *)
Definition vfi_stk : YP09.region := YP09.mkRegion (Some 2%nat) (- VFI_K) 0 (- VFI_K) 0 [].
Definition vfi_mem : smem := vfi_stk :: map ro_region vfi_rodata.
Definition vfi_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] [].
Definition vfi0 : sstate := mkSS A_VFPI sr_atoms vfi_mem None vfi_facts.
(* entry .. printf_common: prologue, TryAsanInitFromRtl, check_printf, aq *)
Definition v1_e : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_g FUEL A_PCOM vfi0).
Lemma r_v1 : sym_run_toN tfibsegs tbl_g FUEL A_PCOM vfi0 = (v1_e, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition v1_r0 : YP09.region := Eval vm_compute in hd vfi_stk (ss_mem v1_e).
Definition v1_rest : smem := Eval vm_compute in tl (ss_mem v1_e).
(* printf_common's return .. REAL (vfprintf) *)
Definition v2_s : sstate := kafter 32 v1_e RA_PCOM_VFPI (-48) 0 0.
Definition v2_e : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_g FUEL A_VFP v2_s).
Lemma r_v2 : sym_run_toN tfibsegs tbl_g FUEL A_VFP v2_s = (v2_e, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition v2_r0 : YP09.region := Eval vm_compute in hd vfi_stk (ss_mem v2_e).
Definition v2_rest : smem := Eval vm_compute in tl (ss_mem v2_e).
(* the image cells are dropped before musl vfprintf (the epilogue reads none) *)
Definition v3_c : sstate := set_mem v2_e [v2_r0].
(* vfprintf's return .. ret *)
Definition v3_s : sstate := kafter 48 v3_c RA_VFP (-48) 0 0.
Definition v3_e : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_g FUEL v3_s).
Lemma r_v3 : sym_runN tfibsegs tbl_g FUEL v3_s = (v3_e, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.

(* the shapes the proof reads off the states *)
Definition vfi_winb (t : option nat * Z * Z) : bool :=
match t with
| (Some 2%nat, lo, hi) => (- VFI_K <=? lo) && (hi <=? 0)
| (_, lo, hi) => hi <=? lo
end.
Definition vfi_win (rs : smem) : bool := forallb vfi_winb (windows rs).
Definition vfi_stk0 (rs : smem) : bool :=
match rs with
| r :: _ => match YP09.r_base r with Some 2%nat => (YP09.r_wlo r =? - VFI_K) && (YP09.r_whi r =? 0) | _ => false end
| [] => false
end.
Definition ro_far (r : YP09.region) : bool :=
match YP09.r_base r with
| None => (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 2 ^ 40) && (YP09.r_whi r <=? YP09.r_wlo r)
| Some _ => false
end.
Definition CS_REGS : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition regs_kept (ss : sstate) : bool :=
forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) CS_REGS.

Lemma vfi_win0 : vfi_win (ss_mem vfi0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v1_pc : ss_pc v1_e = A_PCOM. Proof. vm_compute. reflexivity. Qed.
Lemma v1_resv : ss_resv v1_e = None. Proof. vm_compute. reflexivity. Qed.
Lemma v1_ra : sr_get (ss_regs v1_e) 1 = SLit RA_PCOM_VFPI. Proof. vm_compute. reflexivity. Qed.
Lemma v1_sp : sr_get (ss_regs v1_e) 2 = SOff 2 (-48). Proof. vm_compute. reflexivity. Qed.
Lemma v1_r3 : sr_get (ss_regs v1_e) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma v1_r4 : sr_get (ss_regs v1_e) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma v1_r11 : sr_get (ss_regs v1_e) 11 = SOff 11 0. Proof. vm_compute. reflexivity. Qed.
Lemma v1_r12 : sr_get (ss_regs v1_e) 12 = SOff 12 0. Proof. vm_compute. reflexivity. Qed.
Lemma v1_mem : ss_mem v1_e = v1_r0 :: v1_rest. Proof. vm_compute. reflexivity. Qed.
Lemma v1_b : YP09.r_base v1_r0 = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma v1_lo : YP09.r_lo v1_r0 = - VFI_K. Proof. vm_compute. reflexivity. Qed.
Lemma v1_hi : YP09.r_hi v1_r0 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma v1_wlo : YP09.r_wlo v1_r0 = - VFI_K. Proof. vm_compute. reflexivity. Qed.
Lemma v1_whi : YP09.r_whi v1_r0 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma v1_at : ss_atoms_lt 32 v1_e = true. Proof. vm_compute. reflexivity. Qed.
Lemma v1_wf : regions_wf (ss_mem (kafter 32 v1_e RA_PCOM_VFPI (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v1_nc : no_cdata (ss_mem (kafter 32 v1_e RA_PCOM_VFPI (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v1_ma : mem_atoms_lt 32 (ss_mem (kafter 32 v1_e RA_PCOM_VFPI (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v1_ci : forallb (chunk_inside v1_r0) (YP09.r_chunks v1_r0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v1_far : forallb ro_far v1_rest = true. Proof. vm_compute. reflexivity. Qed.
Lemma v1_stk : vfi_stk0 (ss_mem v1_e) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v2_win : vfi_win (ss_mem v2_s) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v2_stk : vfi_stk0 (ss_mem v2_e) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v2_mem : ss_mem v2_e = v2_r0 :: v2_rest. Proof. vm_compute. reflexivity. Qed.
Lemma v2_b : YP09.r_base v2_r0 = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma v2_lo : YP09.r_lo v2_r0 = - VFI_K. Proof. vm_compute. reflexivity. Qed.
Lemma v2_hi : YP09.r_hi v2_r0 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma v2_wlo : YP09.r_wlo v2_r0 = - VFI_K. Proof. vm_compute. reflexivity. Qed.
Lemma v2_whi : YP09.r_whi v2_r0 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_pc : ss_pc v3_c = A_VFP. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_resv : ss_resv v3_c = None. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_mem : ss_mem v3_c = [v2_r0]. Proof. reflexivity. Qed.
Lemma v3c_ra : sr_get (ss_regs v3_c) 1 = SLit RA_VFP. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_sp : sr_get (ss_regs v3_c) 2 = SOff 2 (-48). Proof. vm_compute. reflexivity. Qed.
Lemma v3c_r3 : sr_get (ss_regs v3_c) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_r4 : sr_get (ss_regs v3_c) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_r10 : sr_get (ss_regs v3_c) 10 = SOff 10 0. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_r11 : sr_get (ss_regs v3_c) 11 = SOff 11 0. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_r12 : sr_get (ss_regs v3_c) 12 = SOff 12 0. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_at : ss_atoms_lt 48 v3_c = true. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_wf : regions_wf (ss_mem (kafter 48 v3_c RA_VFP (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_nc : no_cdata (ss_mem (kafter 48 v3_c RA_VFP (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_ma : mem_atoms_lt 48 (ss_mem (kafter 48 v3_c RA_VFP (-48) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v3c_ci : forallb (chunk_inside v2_r0) (YP09.r_chunks v2_r0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v3s_win : vfi_win (ss_mem v3_s) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v3e_stk : vfi_stk0 (ss_mem v3_e) = true. Proof. vm_compute. reflexivity. Qed.
Lemma v3e_resv : ss_resv v3_e = None. Proof. vm_compute. reflexivity. Qed.
Lemma v3e_ret : clookup tbl_g (ss_pc v3_e) = Some RET_WORD_r. Proof. vm_compute. reflexivity. Qed.
Lemma v3e_ra : sr_get (ss_regs v3_e) 1 = SOff 1 0. Proof. vm_compute. reflexivity. Qed.
Lemma v3e_r10 : sr_get (ss_regs v3_e) 10 = SOff 52 0. Proof. vm_compute. reflexivity. Qed.
Lemma v3e_kept : regs_kept v3_e = true. Proof. vm_compute. reflexivity. Qed.
End r.

(* ---- general lemmas of the walk ---- *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma vfi_win_sound : forall E rs a, vfi_win rs = true -> in_wrange E rs a ->
  bv_unsigned (ew E 2) - VFI_K <= a < bv_unsigned (ew E 2).
Proof.
intros E rs a Hw Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr).
unfold vfi_win in Hw. rewrite forallb_forall in Hw. specialize (Hw _ Ht). unfold vfi_winb in Hw.
destruct b as [[|[|[|n]]]|]; cbn [base_val] in Hr; cbn in Hw; try (apply Z.leb_le in Hw; lia).
apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold VFI_K in *. lia.
Qed.
(* a run whose writable windows lie in the stack window keeps every present byte present *)
Lemma vfi_present : forall (Hd : word -> bool) E rs ss1 ms1 (m : word -> option byte) a,
  vfi_win rs = true -> vfi_stk0 (ss_mem ss1) = true -> TFIB_IMG_END <= bv_unsigned (ew E 2) - VFI_K ->
  frame_of E rs m (ms_mem ms1) -> st_ok tfibsegs E ss1 (restrict Hd ms1) ->
  0 <= a < 2 ^ 64 -> apresent Hd m a -> apresent Hd (ms_mem ms1) a.
Proof.
intros Hd E rs ss1 ms1 m a Hw Hs Hlo HF HS Ha Hp.
destruct (ss_mem ss1) as [|r1 rest] eqn:Hm; [discriminate|].
unfold vfi_stk0 in Hs. destruct (YP09.r_base r1) as [[|[|[|n]]]|] eqn:Hb; cbn in Hs; try discriminate.
apply andb_prop in Hs as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
assert (OUT : ~ (bv_unsigned (ew E 2) - VFI_K <= a < bv_unsigned (ew E 2)) -> apresent Hd (ms_mem ms1) a).
{ intros Hn. apply (apresent_same Hd m); [|exact Hp]. apply HF. rewrite unsigned_lit_small by lia.
  intros Hin. exact (Hn (vfi_win_sound E rs a Hw Hin)). }
destruct (Z_lt_le_dec a (bv_unsigned (ew E 2) - VFI_K)) as [L|L]; [apply OUT; lia|].
destruct (Z_lt_le_dec a (bv_unsigned (ew E 2))) as [L2|L2]; [|apply OUT; lia].
apply (st_ok_window_apresent Hd E ss1 ms1 0 r1 a HS); [rewrite Hm; reflexivity | rewrite Hb, H1, H2; cbn [base_val]; lia | lia].
Qed.
(* keep the first region (the stack) only *)
Lemma st_ok_first : forall E ss ms r0 rest, st_ok tfibsegs E ss ms -> ss_mem ss = r0 :: rest ->
  st_ok tfibsegs E (set_mem ss [r0]) ms.
Proof.
intros E ss ms r0 rest (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_prop in Hwf as [Ha _]. rewrite Ha. reflexivity.
- constructor; [exact (Forall_inv Hok) | constructor].
- cbn. tauto.
Qed.
Lemma ro_far_sound : forall E rs r a, forallb ro_far rs = true -> In r rs ->
  (base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 40) /\
  ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r).
Proof.
intros E rs r a Hf Hin. rewrite forallb_forall in Hf. specialize (Hf r Hin). unfold ro_far in Hf.
destruct (YP09.r_base r); [discriminate|]. cbn [base_val].
apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. split; lia.
Qed.
(* The image constants are cells below SHADOW_OFF, where `unpoison U mem` reads `mem` (the proof of a Theorem Labs
   lane's ro_region_low). *)
Definition vfi_ro_low (l : list (Z * Z * list (Z * BinNums.N * Z))) : bool :=
forallb (fun r => forallb (fun c => (0 <=? fst (fst r) + fst (fst c)) &&
(fst (fst r) + fst (fst c) + Z.of_N (snd (fst c)) <=? SHADOW_OFF)) (snd r)) l.
Lemma vfi_ro_region_low : forall l E (m m' : word -> option byte), vfi_ro_low l = true ->
(forall w : word, bv_unsigned w < SHADOW_OFF -> m' w = m w) ->
Forall (region_ok tfibsegs E m) (map ro_region l) -> Forall (region_ok tfibsegs E m') (map ro_region l).
Proof.
intros l E m m' Hl Hm HF. unfold vfi_ro_low in Hl. rewrite forallb_forall in Hl.
rewrite Forall_forall in HF. apply Forall_map. rewrite Forall_forall. intros [[base sz] cs] Hin.
specialize (Hl _ Hin). specialize (HF _ (in_map ro_region _ _ Hin)). cbn [fst snd] in Hl. rewrite forallb_forall in Hl.
destruct HF as (B1 & B2 & Hw & Hc).
unfold ro_region, region_ok in *. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *.
split; [exact B1|]. split; [exact B2|]. split; [intros o Ho; exfalso; lia|].
rewrite Forall_forall in Hc. apply Forall_map. rewrite Forall_forall. intros [[off n] v] Hc'.
specialize (Hl _ Hc'). specialize (Hc _ (in_map (ro_chunk base) _ _ Hc')). cbn [fst snd] in Hl. apply andb_prop in Hl as [L1 L2].
apply Z.leb_le in L1. apply Z.leb_le in L2.
intros i Hi. destruct (Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
unfold ro_chunk, c_len in *. cbn [YP09.c_off YP09.c_val cv_len fst snd] in *.
unfold mbyte in *. rewrite Hm; [exact Hb2|]. unfold SHADOW_OFF in *. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma sv_atom : forall E n (regs : bvmap 5 word) (r : bv 5), ew E n = getr regs r -> sv_denot E (SOff n 0) = getr regs r.
Proof. intros E n regs r He. cbn [sv_denot]. rewrite Z.add_0_r, He, Z_to_bv_bv_unsigned. reflexivity. Qed.
(* the callee-saved registers of a final state that holds them as the entry atoms *)
Lemma vfi_preserved : forall (Hd : word -> bool) E ss ms (regs : bvmap 5 word),
  st_ok tfibsegs E ss (restrict Hd ms) -> regs_kept ss = true ->
  (forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> (i < 32)%nat -> ew E i = getr regs r) ->
  aregs_preserved regs (ms_regs ms).
Proof.
intros Hd E ss ms regs HS Hk HE r Hr.
assert (Hin : In r CS_REGS) by (unfold acallee_saved in Hr; unfold CS_REGS; cbn [In]; lia).
assert (Hr32 : 0 <= r < 32) by (unfold CS_REGS in Hin; cbn [In] in Hin; lia).
unfold regs_kept in Hk. rewrite forallb_forall in Hk. specialize (Hk r Hin). apply sv_eqb_eq in Hk.
rewrite (st_ok_reg_denot Hd E ss ms _ HS), Hk. apply sv_atom. apply HE; [|lia].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
rewrite Z.mod_small by lia. reflexivity.
Qed.
End h.

(* ---- the contract ---- *)
Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis APCOMMON : apcommon_realizesU B A_PCOM.
Hypothesis AVFP : avfp_realizes B A_VFP.
Theorem avfpi_ok : avfpi_realizes B A_VFPI.
Proof.
intros ly S U W regs mem md sp0 D N M f ps P args out HPRE HREG G10 G11 G12 HFILE.
pose proof HPRE as (Hbase & _ & _ & Hin & _ & HP1 & HP2 & _ & _ & HM & HN & Hdst).
pose proof Hbase as (HA & Hac & H44 & H16 & Hlo & Hhi & H47 & Hkh & Hband & _).
pose proof Hdst as (HD0 & HDac & _).
destruct HREG as (Hra & G2 & G3 & G4).
assert (HSS : SNK_STK = 9104) by reflexivity. assert (HKK : VFI_K = 9152) by reflexivity.
assert (HSP : STK_PCOM = 8192) by reflexivity. assert (HIE : TFIB_IMG_END = 6254592) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity. assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity.
assert (EEr : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Ereg regs []) i = getr regs r)
  by (intros i r Hi; exact (ew_Ereg_nat regs [] i r Hi)).
assert (EE2 : bv_unsigned (ew (Ereg regs []) 2) = sp0 + 48).
{ rewrite (EEr 2%nat 2%bv eq_refl), G2. unfold w64, OSP_VFPI. apply unsigned_lit_small. lia. }
(* the windows of the walk's runs lie in the band below the entry sp; they keep presence *)
assert (WIN : forall E rs a (XW : Z -> Prop), vfi_win rs = true -> bv_unsigned (ew E 2) = sp0 + 48 ->
  in_wrange E rs a -> snk_band sp0 a /\ (a < sp0 + 48 \/ XW a)).
{ intros E rs a XW Hw H2 Hi. pose proof (vfi_win_sound E rs a Hw Hi) as X. rewrite H2 in X.
  split; [unfold snk_band; lia | left; lia]. }
assert (PRES : forall E rs ss1 ms1 m, vfi_win rs = true -> vfi_stk0 (ss_mem ss1) = true ->
  bv_unsigned (ew E 2) = sp0 + 48 -> frame_of E rs m (ms_mem ms1) -> st_ok tfibsegs E ss1 (restrict (w_H W) ms1) ->
  (forall a, snk_band sp0 a -> apresent (w_H W) m a) -> forall a, snk_band sp0 a -> apresent (w_H W) (ms_mem ms1) a).
{ intros E rs ss1 ms1 m Hw Hs H2 HF HS Hp a Ha.
  apply (vfi_present (w_H W) E rs ss1 ms1 m a Hw Hs); [rewrite H2; lia | exact HF | exact HS | unfold snk_band in Ha; lia | exact (Hp a Ha)]. }
(* gl_pre and the FILE at a memory the walk changed only below sp0 + 0x30 *)
assert (XFER : forall m' md', snk_frame B ly S U W mem md sp0 (sp0 + 48) (fun _ => False) m' md' ->
  gl_pre B ly S U W m' md' sp0 D N M f ps P args out /\ vsn_file W m' sp0 D N).
{ intros m' md' (HA' & _ & Hp' & Hfr' & Hpm').
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < sp0 + 48) ->
    aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) mem a) by (intros a Ha Hn; apply Hfr'; [exact Ha | exact Hn | tauto]).
  assert (KD : aview tfibsegs (w_H W) m' D = aview tfibsegs (w_H W) mem D) by (apply KEEP; lia).
  split.
  - apply (gl_pre_xfer B LAWS TB ly S U W mem md m' md' sp0 D N M f ps P args out HPRE HA' Hp'); [| left; exact KD | exact Hpm'].
    intros a Ha Hn _. apply KEEP; [exact Ha | lia].
  - apply (vsn_file_xfer W mem m' sp0 D N HFILE); [| exact KD].
    intros a Ha. unfold CKO, FO in Ha. apply KEEP; lia. }
(* the entry state *)
assert (HS0 : st_ok tfibsegs (Ereg regs []) vfi0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_VFPI) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold vfi0. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
    + unfold vfi_stk. apply (region_ok_stack tfibsegs (Ereg regs []) _ 2 (sp0 + 48) (- VFI_K)); [exact EE2 | lia | lia |].
      intros a Ha. apply apresent_writable. apply Hband. unfold snk_band. lia.
    + apply (vfi_ro_region_low vfi_rodata (Ereg regs []) (mrestrict (w_H W) (unpoison U mem))); [vm_compute; reflexivity | |].
      * intros w Hw. unfold mrestrict. rewrite (ARU_mem_low tfibsegs B ly S U W mem md w HA Hw). reflexivity.
      * exact (rodata_ok B TB vfi_rodata ly S (w_H W) (unpoison U mem) (Ereg regs []) (vfi_rodata_chk ly)
          (ARU_ARm tfibsegs B ly S U W mem md HA)).
  - apply pairwise_disjoint_of_extents. unfold vfi_mem, vfi_stk, vfi_rodata, icpt_rodata, ro_region, extent_of_region.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. unfold vfi_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite EE2. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
    rewrite Z.add_mod, H16 by lia. reflexivity. }
assert (F0 : snk_frame B ly S U W mem md sp0 (sp0 + 48) (fun _ => False) mem md)
  by (apply (g_frame_init B ly S U W mem md sp0 (sp0 + 48) _ Hbase); lia).
unfold cfg_at, w64.
(* run 1: entry .. printf_common *)
eapply SRr_bind; [exact (g_phase_to W (Ereg regs []) A_PCOM vfi0 v1_e RS_running _ md HS0 r_v1)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
assert (HS1' : st_ok tfibsegs (Ereg regs []) v1_e (restrict (w_H W) ms1)) by exact HS1. clear HS1.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (F1 : snk_frame B ly S U W mem md sp0 (sp0 + 48) (fun _ => False) (ms_mem ms1) md1).
{ apply (g_frame_run B LAWS ly S U W mem md sp0 (sp0 + 48) (fun _ => False) Hbase mem md (ms_mem ms1) mat1 (Ereg regs [])
    (ss_mem vfi0) F0); [intros a Ha; exact (WIN _ _ a _ vfi_win0 EE2 Ha) | exact HF1 |].
  exact (PRES _ _ v1_e ms1 mem vfi_win0 v1_stk EE2 HF1 HS1' Hband). }
pose proof F1 as (F1a & _ & F1p & _ & F1m).
pose proof (XFER _ _ F1) as (PRE1 & _).
pose proof PRE1 as (_ & Hrom1 & _ & _ & _ & _ & _ & Hsl1 & Hfr1 & _).
assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 RA_PCOM_VFPI) by exact (g_reg W _ v1_e ms1 1 _ HS1' v1_ra).
assert (RA1 : raZ (ms_regs ms1) = RA_PCOM_VFPI) by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold RA_PCOM_VFPI; lia).
assert (Sp1 : spZ (ms_regs ms1) = sp0).
{ unfold spZ. rewrite (g_reg W _ v1_e ms1 2 _ HS1' v1_sp). cbn [sv_denot]. rewrite EE2. rewrite unsigned_lit_small by lia. lia. }
assert (R13 : getr (ms_regs ms1) 3 = w64 (as_gp B))
  by (rewrite (g_reg W _ v1_e ms1 3 _ HS1' v1_r3), (sv_atom _ 3 regs 3 (EEr 3%nat 3%bv eq_refl)); exact G3).
assert (R14 : getr (ms_regs ms1) 4 = w64 (as_tp B))
  by (rewrite (g_reg W _ v1_e ms1 4 _ HS1' v1_r4), (sv_atom _ 4 regs 4 (EEr 4%nat 4%bv eq_refl)); exact G4).
assert (R111 : getr (ms_regs ms1) 11 = w64 f)
  by (rewrite (g_reg W _ v1_e ms1 11 _ HS1' v1_r11), (sv_atom _ 11 regs 11 (EEr 11%nat 11%bv eq_refl)); exact G11).
assert (R112 : getr (ms_regs ms1) 12 = w64 P)
  by (rewrite (g_reg W _ v1_e ms1 12 _ HS1' v1_r12), (sv_atom _ 12 regs 12 (EEr 12%nat 12%bv eq_refl)); exact G12).
(* call printf_common (ctx, fmt, aq): its window [sp0 - STK_PCOM, sp0) *)
eapply SRr_bind.
{ apply (kcall W (Ereg regs []) v1_e ms1 md1 (sp0 + 48) VFI_K v1_r0 v1_rest 32 RA_PCOM_VFPI (-48) 0 0 STK_PCOM
    (fun _ => False) (fun regs2 mem2 md2 => ARU tfibsegs B ly S U W mem2 md2)
    HS1' v1_resv EE2 v1_mem v1_b v1_lo v1_hi ltac:(rewrite v1_wlo; lia) ltac:(rewrite v1_whi; lia) v1_ra v1_sp
    v1_at v1_wf v1_nc v1_ma v1_ci); try lia.
  - intros r a Hr Ha. destruct (ro_far_sound (Ereg regs []) _ r a v1_far Hr) as [X _]. specialize (X Ha).
    split; [lia | split; [lia | tauto]].
  - intros r a Hr Ha. exfalso. destruct (ro_far_sound (Ereg regs []) _ r a v1_far Hr) as [_ X]. exact (X Ha).
  - intros a Ha. apply F1p. unfold snk_band. lia.
  - rewrite v1_pc. eapply SRr_mono.
    { apply (APCOMMON ly S U W (ms_regs ms1) (ms_mem ms1) md1 f ps P args D N out); rewrite ?Sp1; try lia;
        first [exact Hrom1 | exact R111 | exact R112 | exact Hin | exact Hsl1 | exact Hfr1
        | (intros a Ha; apply F1p; unfold snk_band; lia) | idtac].
      apply (g_ecall_preU B ly S U W (ms_regs ms1) (ms_mem ms1) md1 F1a); rewrite ?Sp1; try lia;
        first [exact R13 | exact R14 | exact H16 | (intros a Ha; apply F1p; unfold snk_band; lia)
        | (rewrite R1; apply ret_ok_lit; [unfold RA_PCOM_VFPI; lia | reflexivity])]. }
    cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HA2 & HP2' & Hsb2 & Hfr2 & Hpm2).
    split; [reflexivity|]. exists regs2, mem2, md2. rewrite RA1.
    split; [reflexivity|]. split; [exact HP2'|]. split; [exact Hsb2|].
    split; [intros a Ha Hn _; apply Hfr2; [exact Ha | rewrite Sp1; lia]|].
    split; [exact Hpm2 | exact HA2]. }
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & _ & Hfr2 & Hpm2 & HA2).
set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *.
set (E2 := havoc (Ereg regs []) 32 (map (getr (ms_regs ms2)) CLOB)) in HS2.
assert (E2r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> (i < 32)%nat -> ew E2 i = getr regs r).
{ intros i r Hi Hl. subst E2. rewrite ew_havoc_old by lia. exact (EEr i r Hi). }
assert (E22 : bv_unsigned (ew E2 2) = sp0 + 48) by (subst E2; rewrite ew_havoc_old by lia; exact EE2).
assert (F2 : snk_frame B ly S U W mem md sp0 (sp0 + 48) (fun _ => False) (ms_mem ms2) md2).
{ apply (g_frame_step B ly S U W mem md sp0 (sp0 + 48) (fun _ => False) _ _ _ _ F1 HA2).
  - apply with_vm_backing_same.
  - intros a Ha. apply Hpm2. apply F1p. exact Ha.
  - intros a Ha Hn _. apply Hfr2; [exact Ha | lia | tauto].
  - exact Hpm2. }
(* run 2: printf_common's return .. REAL (vfprintf) *)
eapply SRr_bind; [exact (g_phase_to W E2 A_VFP v2_s v2_e RS_running ms2 md2 HS2 r_v2)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
assert (HS3' : st_ok tfibsegs E2 v2_e (restrict (w_H W) ms3)) by exact HS3. clear HS3.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2).
pose proof F2 as (_ & _ & F2p & _ & _).
assert (F3 : snk_frame B ly S U W mem md sp0 (sp0 + 48) (fun _ => False) (ms_mem ms3) md3).
{ apply (g_frame_run B LAWS ly S U W mem md sp0 (sp0 + 48) (fun _ => False) Hbase (ms_mem ms2) md2 (ms_mem ms3) mat3 E2
    (ss_mem v2_s) F2); [intros a Ha; exact (WIN _ _ a _ v2_win E22 Ha) | exact HF3 |].
  exact (PRES _ _ v2_e ms3 (ms_mem ms2) v2_win v2_stk E22 HF3 HS3' F2p). }
pose proof F3 as (_ & _ & F3p & _ & _).
pose proof (XFER _ _ F3) as (PRE3 & FILE3).
pose proof (st_ok_first E2 v2_e _ v2_r0 v2_rest HS3' v2_mem) as HS3c. fold v3_c in HS3c.
assert (R31 : getr (ms_regs ms3) 1 = Z_to_bv 64 RA_VFP) by exact (g_reg W _ v3_c ms3 1 _ HS3c v3c_ra).
assert (RA3 : raZ (ms_regs ms3) = RA_VFP) by (unfold raZ; rewrite R31; apply unsigned_lit_small; unfold RA_VFP; lia).
assert (R32 : getr (ms_regs ms3) 2 = w64 sp0).
{ rewrite (g_reg W _ v3_c ms3 2 _ HS3c v3c_sp). cbn [sv_denot]. rewrite E22. unfold w64. f_equal. lia. }
assert (R33 : getr (ms_regs ms3) 3 = w64 (as_gp B))
  by (rewrite (g_reg W _ v3_c ms3 3 _ HS3c v3c_r3), (sv_atom _ 3 regs 3 (E2r 3%nat 3%bv eq_refl ltac:(lia))); exact G3).
assert (R34 : getr (ms_regs ms3) 4 = w64 (as_tp B))
  by (rewrite (g_reg W _ v3_c ms3 4 _ HS3c v3c_r4), (sv_atom _ 4 regs 4 (E2r 4%nat 4%bv eq_refl ltac:(lia))); exact G4).
assert (R310 : getr (ms_regs ms3) 10 = w64 (sp0 + FO))
  by (rewrite (g_reg W _ v3_c ms3 10 _ HS3c v3c_r10), (sv_atom _ 10 regs 10 (E2r 10%nat 10%bv eq_refl ltac:(lia))); exact G10).
assert (R311 : getr (ms_regs ms3) 11 = w64 f)
  by (rewrite (g_reg W _ v3_c ms3 11 _ HS3c v3c_r11), (sv_atom _ 11 regs 11 (E2r 11%nat 11%bv eq_refl ltac:(lia))); exact G11).
assert (R312 : getr (ms_regs ms3) 12 = w64 P)
  by (rewrite (g_reg W _ v3_c ms3 12 _ HS3c v3c_r12), (sv_atom _ 12 regs 12 (E2r 12%nat 12%bv eq_refl ltac:(lia))); exact G12).
(* call musl vfprintf (f, fmt, ap): the band below sp0, the FILE and the destination *)
eapply SRr_bind.
{ apply (kcall W E2 v3_c ms3 md3 (sp0 + 48) VFI_K v2_r0 [] 48 RA_VFP (-48) 0 0 SNK_STK (vf_xw sp0 D M)
    (fun regs4 mem4 md4 => snk_frame B ly S U W (ms_mem ms3) md3 sp0 sp0 (vf_xw sp0 D M) mem4 md4 /\
       getr regs4 10 = w64 (Z.of_nat (length out)) /\
       (forall i, 0 <= i <= Z.of_nat (length out) ->
          aview tfibsegs (w_H W) mem4 (D + i) = Some (nth (Z.to_nat i) (out ++ [0]) 0)))
    HS3c v3c_resv E22 v3c_mem v2_b v2_lo v2_hi ltac:(rewrite v2_wlo; lia) ltac:(rewrite v2_whi; lia) v3c_ra v3c_sp
    v3c_at v3c_wf v3c_nc v3c_ma v3c_ci); try lia;
    first [ solve [intros a Hx Ha; exfalso; destruct Hx as [Hx|Hx]; unfold dst_xw, FO, CKO in *; lia]
          | solve [intros r a Hr; destruct Hr]
          | solve [intros a Ha; apply F3p; unfold snk_band; lia]
          | idtac ].
  - rewrite v3c_pc. eapply SRr_mono.
    { apply (AVFP ly S U W (ms_regs ms3) (ms_mem ms3) md3 sp0 D N M f ps P args out PRE3); [|exact R310 | exact R311 | exact R312 | exact FILE3].
      unfold snk_regs. split; [rewrite R31; apply ret_ok_lit; [unfold RA_VFP; lia | reflexivity]|].
      split; [exact R32|]. split; [exact R33 | exact R34]. }
    unfold gl_post. cbv beta. intros W' c' _ (-> & regs4 & mem4 & md4 & -> & HF4 & HP4 & H10 & HDb).
    split; [reflexivity|]. exists regs4, mem4, md4. rewrite RA3.
    pose proof HF4 as (_ & Hsb4 & _ & Hfr4 & Hpm4).
    split; [reflexivity|]. split; [exact HP4|]. split; [exact Hsb4|].
    split; [intros a Ha Hn Hx; apply Hfr4; [exact Ha | lia | exact Hx]|].
    split; [exact Hpm4|]. split; [exact HF4|]. split; [exact H10 | exact HDb]. }
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & _ & _ & _ & (HF4 & H10 & HDb)).
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
set (E4 := havoc E2 48 (map (getr (ms_regs ms4)) CLOB)) in HS4.
assert (E4r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> (i < 32)%nat -> ew E4 i = getr regs r).
{ intros i r Hi Hl. subst E4. rewrite ew_havoc_old by lia. exact (E2r i r Hi Hl). }
assert (E42 : bv_unsigned (ew E4 2) = sp0 + 48) by (subst E4; rewrite ew_havoc_old by lia; exact E22).
assert (F4 : snk_frame B ly S U W mem md sp0 (sp0 + 48) (vf_xw sp0 D M) (ms_mem ms4) md4).
{ pose proof F3 as (Fa & Fs & Fp & Ff & Fm). pose proof HF4 as (Ga & Gs & Gp & Gf & Gm).
  assert (F3w : snk_frame B ly S U W mem md sp0 (sp0 + 48) (vf_xw sp0 D M) (ms_mem ms3) md3).
  { split; [exact Fa|]. split; [exact Fs|]. split; [exact Fp|]. split; [|exact Fm].
    intros a Ha Hn _. apply Ff; [exact Ha | exact Hn | tauto]. }
  apply (g_frame_step B ly S U W mem md sp0 (sp0 + 48) (vf_xw sp0 D M) _ _ _ _ F3w Ga Gs Gp); [|exact Gm].
  intros a Ha Hn Hx. apply Gf; [exact Ha | lia | exact Hx]. }
pose proof F4 as (_ & _ & F4p & _ & _).
(* run 3: vfprintf's return .. ret *)
eapply SRr_bind; [exact (g_phase W E4 v3_s v3_e (RS_stopped (SR_jalr (SOff 1 0))) ms4 md4 HS4 r_v3)|].
intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5).
assert (HS5' : st_ok tfibsegs E4 v3_e (restrict (w_H W) ms5)) by exact HS5. clear HS5.
apply (g_ret W E4 v3_e ms5 (with_vm_backing (m_vm_lazy md4) mat5 md4) _ HS5' v3e_resv v3e_ret).
intros mat'. rewrite (wvb_collapse (m_vm_lazy md4) mat' mat5 md4).
assert (F5 : snk_frame B ly S U W mem md sp0 (sp0 + 48) (vf_xw sp0 D M) (ms_mem ms5)
  (with_vm_backing (m_vm_lazy md4) mat' md4)).
{ apply (g_frame_run B LAWS ly S U W mem md sp0 (sp0 + 48) (vf_xw sp0 D M) Hbase (ms_mem ms4) md4 (ms_mem ms5) mat' E4
    (ss_mem v3_s) F4); [intros a Ha; exact (WIN _ _ a _ v3s_win E42 Ha) | exact HF5 |].
  exact (PRES _ _ v3_e ms5 (ms_mem ms4) v3s_win v3e_stk E42 HF5 HS5' F4p). }
assert (R51 : getr (ms_regs ms5) 1 = getr regs 1)
  by (rewrite (g_reg W _ v3_e ms5 1 _ HS5' v3e_ra); exact (sv_atom _ 1 regs 1 (E4r 1%nat 1%bv eq_refl ltac:(lia)))).
assert (R510 : getr (ms_regs ms5) 10 = w64 (Z.of_nat (length out))).
{ rewrite (g_reg W _ v3_e ms5 10 _ HS5' v3e_r10). cbn [sv_denot].
  pose proof (ew_havoc_new E2 48 (map (getr (ms_regs ms4)) CLOB) 4 (Z_to_bv 64 0) ltac:(unfold CLOB; cbn [map length]; lia)) as X.
  cbn [Nat.add] in X. fold E4 in X. rewrite X. unfold CLOB. cbn [map nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  exact H10. }
unfold gl_post. split; [reflexivity|]. exists (ms_regs ms5), (ms_mem ms5), (with_vm_backing (m_vm_lazy md4) mat' md4).
split.
{ unfold cfg_at. rewrite R51. unfold YK0s.ret_ok in Hra. rewrite Hra. unfold w64, raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact F5|].
split; [exact (vfi_preserved (w_H W) E4 v3_e ms5 regs HS5' v3e_kept E4r)|].
split; [exact R510|].
intros i Hi. rewrite (aview_same (w_H W) (ms_mem ms4) (ms_mem ms5) (D + i)); [exact (HDb i Hi)|].
apply HF5. rewrite unsigned_lit_small by lia. intros Hw.
pose proof (vfi_win_sound E4 _ _ v3s_win Hw) as X. rewrite E42 in X. lia.
Qed.
End v.
