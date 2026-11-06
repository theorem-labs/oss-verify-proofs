(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 463 of its 516 lines of code are new or changed and 878 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: the walk of the
   phase NP_ts (listing offset 0x1394, address 0x81b1c) to NP_exit (0x112c, 0x818b4). The phase stores the
   record's timestamp into the caller's cell when the caller asked for one, and sets the word the call returns.
   Its entry predicate is nx_ts_inv (lib/B/Prog/PcapSourceNextFitBDefs.v); its exit predicate is lib/B's
   nx_exit_inv (lib/B/Prog/PcapSourceNextDefs.v). The lib/B twin of lib/A/Prog/PcapSourceNextFitB.v (a Theorem Labs lane):
   the same steps over lib/B's registers, listing and phase layer.

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; symbols from its unstripped twin fuzz_pcap.asan-ubsan (sha256 c969d83cdd59),
   capstone 5 disassembly; the slot table nxb-handoff.md (sha256 c02dc85fade1; internal record)).

   THE RUN. The engine (PcapPaLib.paj_run_to over lib/B's listing) walks the 18 slots 0x81b1c .. 0x81b60 from a
   symbolic state whose registers are the atoms of the machine registers (sr_atoms) and whose memory is the
   caller's 8-byte cell at a7 = ts (atom 17, writable; only when ts <> 0). The shadow base is t0 (atom 5,
   reloaded from NS_SB on every path into NP_ts), so the shadow entry (17, 0, 8) is read against Bx = atom 5.
   The atom facts say t0 = 0x7fff8000, and ts = 0, or 4096 <= ts <= 2^47 - 8 and ts mod 8 = 0. With them:
   - ts = 0: the engine leaves `beqz a7` (0x81b1c) open, so the walk splits on it (psrr_branch_tok); the
     fall-through arm contradicts ts = 0; the taken arm runs 0x81b58 .. 0x81b60 (no store);
   - ts <> 0: `beqz a7` is not taken (ts >= 4096); the UBSan alignment guard 0x81b20 `andi a0,a7,7` /
     0x81b24 `bnez a0` to the `unimp` NP_trap (0x81b64) is NOT TAKEN: the engine rewrites ts & 7 to 0 from the
     alignment fact (s_and_ptr, Reusable/YP0m.v), the decision lib/B/Prog/PcapSourceClose.v's walk makes for ps
     (its header, 0x81d68), from the premise ts mod 8 = 0 of the statement; the shadow check 0x81b28 .. 0x81b34
     (`bnez a0` to the report path 0x81c30 / __asan_report_store8 0x81c34) is not taken: the shadow byte of ts
     is 0 by range_addressable. No other guard lies in the phase: the timestamp is unsigned arithmetic
     (`mulhu`, `add` on uint64), which UBSan does not instrument, and the store address is a7 itself.
   It stops at NP_exit with
     a0 = mulhu (s2 << 32) (10^6 << 32) + ((s8 << 32) >> 32) stored at ts (when ts <> 0),
     a1 = (s6 << 32) >> 32,
   and a0, a1, s6, s8 changed; every other register is the one it started with (NX_TS_KEEP).
   (0x3d09 << 38 = 15625 * 2^38 = 10^6 * 2^32, so mulhu gives sec * 10^6 for a 32-bit sec, and
   sec * 10^6 + usec < 2^52: the stored word is exactly PSN.rec_ts, no wrap mod 2^64.)

   THE PHASE (pb_nx_ts) takes nx_ts_inv to nx_exit_inv: the run writes only the timestamp cell, which lies in a
   caller's frame, so every word nx_exit_inv reads (the machine frame's slots and saved registers in the stack
   window, the class-0 frame, its shadow, the struct, the buffer, the stream) is kept; a1 is the model's result
   (nx_res_fit) and the cell holds the model's timestamp (nx_tsv_fit). *)
(* Modified by Theorem Labs, 2026-10: Section f's vm_frame / asource_at_frame (a copy of lib/B/Prog/PcapSourceClose.v's,
   over an implicit segs) deleted; their uses here and in PcapSourceNextHdrBKeep.v name lib/A/Prog/PcapSourceCloseSpec.v's
   vm_frame_segs / asource_at_frame_segs. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceMeter PFreadISpec.
(* lib/B's phase layer LAST (it shadows lib/A's phase names). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs PcapSourceNextFitBDefs.
(* The segs-generic frame lemmas, Required without Import and used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state of the phase ---- *)

Definition SB_TS : Z := 0x7fff8000.        (* the shadow base, SHADOW_OFF *)
Definition TBx : sv := SOff 5 0.           (* t0, which holds it at NP_ts *)
Definition TSspan : Z * Z := (SB_TS, SB_TS + 2 ^ 44 - 1).
(* The caller's timestamp cell at a7, writable. *)
Definition R_ts : YP09.region := YP09.mkRegion (Some 17%nat) 0 8 0 8 [].
Definition ts_SH1 : list shent := [mkSHE 17 0 8].
Definition ts_facts1 : facts := mkFacts [(5%nat, mkAF SB_TS SB_TS 0); (17%nat, mkAF 4096 (2 ^ 47 - 8) 3)] [] [].
Definition ss_ts1 : sstate := mkSS NP_ts sr_atoms [R_ts] None ts_facts1.
Definition ts_facts0 : facts := mkFacts [(5%nat, mkAF SB_TS SB_TS 0); (17%nat, mkAF 0 0 0)] [] [].
Definition ss_ts0 : sstate := mkSS NP_ts sr_atoms [] None ts_facts0.
(* The registers the phase does not write: all but a0, a1, s6 and s8. *)
Definition NX_TS_KEEP : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 23; 25; 26; 27; 28; 29; 30; 31]%bv.

(* ---- the values the run computes ---- *)

Lemma U_hi32 : forall E n, U E (SAlu ALU_SLL (SOff n 0) (SLit 32)) = (bv_unsigned (ew E n) mod 2 ^ 32) * 2 ^ 32.
Proof.
  intros E n. rewrite U_SAlu, U_SOff, U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 32) 63) with 32. rewrite Z.add_0_r.
  pose proof (u64_range (ew E n)) as Hx.
  rewrite (zcanon_id (bv_unsigned (ew E n))) by (unfold M64; lia).
  rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
  change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). apply Z.mul_mod_distr_r; lia.
Qed.

(* (x << 32) >> 32: the low word of x (0x81b4c, 0x81b58..0x81b5c). *)
Lemma U_lo32 : forall E n,
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 32)) = bv_unsigned (ew E n) mod 2 ^ 32.
Proof.
  intros E n. rewrite U_SAlu, U_hi32, U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 32) 63) with 32.
  pose proof (Z.mod_pos_bound (bv_unsigned (ew E n)) (2 ^ 32) ltac:(lia)) as Hm.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
  apply zcanon_id. unfold M64. lia.
Qed.

(* The stored timestamp (0x81b38..0x81b50): mulhu (sec << 32) (10^6 << 32) + usec = sec * 10^6 + usec, for the
   low words sec of s2 and usec of s8. *)
Lemma U_tsv : forall E n m,
  U E (SAlu ALU_ADD (SMd M_MULHU (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 4294967296000000))
         (SAlu ALU_SRL (SAlu ALU_SLL (SOff m 0) (SLit 32)) (SLit 32)))
  = (bv_unsigned (ew E n) mod 2 ^ 32) * 1000000 + bv_unsigned (ew E m) mod 2 ^ 32.
Proof.
  intros E n m. rewrite U_SAlu, U_SMd, U_hi32, U_lo32, U_SLit. cbn [zalu_raw zmd_raw].
  change (zcanon 4294967296000000) with 4294967296000000. change (Z.of_N 64) with 64.
  set (s := bv_unsigned (ew E n) mod 2 ^ 32). set (u := bv_unsigned (ew E m) mod 2 ^ 32).
  assert (Hs : 0 <= s < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Hu : 0 <= u < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (s * 2 ^ 32 * 4294967296000000) with (s * 1000000 * 2 ^ 64)
    by (change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); change (2 ^ 32) with 4294967296; ring).
  rewrite Z.div_mul by lia.
  rewrite (zcanon_id (s * 1000000)) by (unfold M64; lia).
  apply zcanon_id. unfold M64. lia.
Qed.

(* A register of the list NX_TS_KEEP. *)
Ltac inkeep := unfold NX_TS_KEEP; cbn [In]; repeat (first [left; reflexivity | right]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- memory facts across a run that changed only some bytes ---- *)

Lemma ts_rdword_keep : forall (W3 : world SEGS) (m m' : word -> option byte) a v,
  (forall i, 0 <= i < 8 -> aview SEGS (w_H W3) m' (a + i) = aview SEGS (w_H W3) m (a + i)) ->
  rdword (aview SEGS (w_H W3) m) a = Some v -> rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
  intros W3 m m' a v K Hr.
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
  pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
  pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
  pose proof (K 7 ltac:(lia)) as K7.
  unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

Lemma ts_vm_keep : forall (W3 : world SEGS) (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W3) m' x = aview SEGS (w_H W3) m x) ->
  val_mem SEGS (rdW W3 m) a n v -> val_mem SEGS (rdW W3 m') a n v.
Proof.
  intros W3 m m' a n v K Hv k Hk.
  rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) m m' (a + Z.of_nat k)) by (apply K; lia).
  exact (Hv k Hk).
Qed.

Lemma ts_garr8_keep : forall (W3 : world SEGS) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W3) m' x = aview SEGS (w_H W3) m x) ->
  garr8 SEGS (rdW W3 m) a l -> garr8 SEGS (rdW W3 m') a l.
Proof.
  intros W3 m m' a l K Hg. apply (garr8_frame SEGS (rdW W3 m) (rdW W3 m') a l Hg).
  intros x Hx. apply (mbyte_of_aview SEGS). apply K. exact Hx.
Qed.

Lemma ts_ps_keep : forall (W3 : world SEGS) (m m' : word -> option byte) ps h sw ol vt vid pad,
  (forall x, ps <= x < ps + PS_LEN -> aview SEGS (w_H W3) m' x = aview SEGS (w_H W3) m x) ->
  nx_ps_at SEGS (rdW W3 m) ps h sw ol vt vid pad -> nx_ps_at SEGS (rdW W3 m') ps h sw ol vt vid pad.
Proof.
  intros W3 m m' ps h sw ol vt vid pad K (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  assert (K' : forall o n, 0 <= o -> o + Z.of_nat n <= 24 ->
    forall x, ps + o <= x < ps + o + Z.of_nat n -> aview SEGS (w_H W3) m' x = aview SEGS (w_H W3) m x).
  { intros o n Ho Hn x Hx. apply K. unfold PS_LEN. lia. }
  unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
  split; [eapply ts_vm_keep; [apply (K' 0 8%nat); [lia | first [lia | cbn; lia]] | exact P1]|].
  split; [eapply ts_vm_keep; [apply (K' 8 4%nat); [lia | first [lia | cbn; lia]] | exact P2]|].
  split; [eapply ts_vm_keep; [apply (K' 12 4%nat); [lia | first [lia | cbn; lia]] | exact P3]|].
  split; [eapply ts_vm_keep; [apply (K' 16 4%nat); [lia | first [lia | cbn; lia]] | exact P4]|].
  split; [eapply ts_vm_keep; [apply (K' 20 2%nat); [lia | first [lia | cbn; lia]] | exact P5]|].
  split; [eapply ts_garr8_keep; [apply (K' 22 (length pad)); [lia | rewrite P7; first [lia | cbn; lia]] | exact P6]|].
  exact P7.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* What the run leaves at NP_exit, from the machine state ms3 at NP_ts. *)
Definition ts_after (W3 : world SEGS) (ms3 ms' : machine_state) (md3 md' : Model) (ts sec usec len : Z) : Prop :=
  ms' = mkst (ms_regs ms') (w64 (BASE + NP_exit)) (ms_mem ms') (seg_rom SEGS) /\
  (forall r, In r NX_TS_KEEP -> getr (ms_regs ms') r = getr (ms_regs ms3) r) /\
  getr (ms_regs ms') 11 = w64 len /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ts <> 0 /\ ts <= a < ts + 8) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) /\
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) /\
  (ts <> 0 -> val_mem SEGS (rdW W3 (ms_mem ms')) ts 8 (sec * 1000000 + usec)) /\
  m_fds md' = m_fds md3 /\ m_fs md' = m_fs md3.

(* The run of the phase, at the machine level. *)
Lemma ts_run : forall (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2
  (ts sec usec len : Z) (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  ms_pc_val ms3 = w64 (BASE + NP_ts) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 5 = w64 SHADOW_OFF ->
  getr (ms_regs ms3) 17 = w64 ts ->
  bv_unsigned (getr (ms_regs ms3) 22) mod 2 ^ 32 = len ->
  bv_unsigned (getr (ms_regs ms3) 18) mod 2 ^ 32 = sec ->
  bv_unsigned (getr (ms_regs ms3) 24) mod 2 ^ 32 = usec ->
  (ts <> 0 ->
     ts mod 8 = 0 /\ 4096 <= ts /\ ts + 8 <= 2 ^ 47 /\ amem_range ts 8 /\
     range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF ts 8 /\
     (forall a, ts <= a < ts + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly3 S3) ly3 own a)) ->
  (forall ms' md',
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms') md' k2 ->
     ts_after W3 ms3 ms' md3 md' ts sec usec len ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros W3 ms3 md3 STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 ts sec usec len Q
    HJ Hpc Hresv Hpend Hrom Hfr Hfcsr H5 H17 H22 H18 H24 HTS HK.
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + NP_ts)) (rdW W3 (ms_mem ms3)) (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0' rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfr, Hfcsr.
    subst. reflexivity. }
  assert (Hts64 : 0 <= ts < 2 ^ 64).
  { destruct (Z.eq_dec ts 0) as [->|T]; [lia|]. destruct (HTS T) as (_ & Hts4 & Hts47 & _). lia. }
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; apply Eimg_low; exact Hn).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | reflexivity]).
  assert (E5 : ew E 5 = Z_to_bv 64 SB_TS)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 5 5%bv eq_refl); exact H5).
  assert (E17 : ew E 17 = Z_to_bv 64 ts)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 17 17%bv eq_refl); exact H17).
  assert (E18 : ew E 18 = getr (ms_regs ms3) 18)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 18 18%bv eq_refl)).
  assert (E22 : ew E 22 = getr (ms_regs ms3) 22)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 22 22%bv eq_refl)).
  assert (E24 : ew E 24 = getr (ms_regs ms3) 24)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 24 24%bv eq_refl)).
  assert (U5 : bv_unsigned (ew E 5) = SB_TS) by (rewrite E5; apply unsigned_lit_small; unfold SB_TS; lia).
  assert (U17 : bv_unsigned (ew E 17) = ts) by (rewrite E17; apply unsigned_lit_small; lia).
  assert (LAND : forall ss (ms : machine_state) mat,
    st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = NP_exit ->
    forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) NX_TS_KEEP = true ->
    sr_get (ss_regs ss) 11 = SAlu ALU_SRL (SAlu ALU_SLL (SOff 22 0) (SLit 32)) (SLit 32) ->
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k2 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (ts <> 0 /\ ts <= a < ts + 8) ->
       aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
    mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms)) ->
    (ts <> 0 -> val_mem SEGS (rdW W3 (ms_mem ms)) ts 8 (sec * 1000000 + usec)) ->
    SRr SEGS W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q).
  { intros ss ms mat HS Hrv Hpc' Hkeep Hr11 HJ' HUN HG' HV.
    apply (HK ms _ HJ'). unfold ts_after.
    split.
    { pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hsh. rewrite Hpc' in Hsh. exact Hsh. }
    split.
    { intros r Hr. pose proof (regs_kept_of_st_ok_pi E ss _ (ms_regs ms3) [] NX_TS_KEEP HS HAE Hkeep r Hr) as Hk.
      cbn [restrict ms_regs] in Hk. exact Hk. }
    split.
    { pose proof (st_ok_pi_restrict_reg (w_H W3) E ss ms 11%bv HS) as R11. rewrite Hr11 in R11.
      rewrite R11, denot_lit_U, U_lo32, E22, H22. reflexivity. }
    split; [exact HUN|]. split; [exact HG'|]. split; [exact HV|].
    destruct md3. split; reflexivity. }
  destruct (Z.eq_dec ts 0) as [T0 | T0].
  - (* ts = 0 *)
    assert (HS : st_ok_pi SEGS VAL E ss_ts0 (restrict (w_H W3) ms3)).
    { rewrite Hms. unfold ss_ts0. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - apply Forall_nil.
      - apply pairwise_disjoint_of_extents. cbn. exact I.
      - split; [|split; [exact I | exact I]].
        cbn [ts_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U5, U17, T0. unfold SB_TS.
        repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia]. }
    assert (SHOK : sh_ok SEGS TBx [] E (rdW W3 (ms_mem ms3))) by (unfold sh_ok; apply Forall_nil).
    clearbody E.
    psrr_branch_tok RUNTO BR HS SHOK TSspan.
    + clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK TSspan NP_exit.
      * lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
          let rs' := eval vm_compute in rs in change rs with rs' end.
        apply awr_ok_nil.
      * eapply LAND; [exact HS | reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact HJ | | exact HG | ].
        -- intros a Ha Hna. apply (kept_of_frame E _ (w_H W3) (ms_mem ms3) (ms_mem ms) (fun _ => False) HFr);
             [| exact Ha | intros []].
           intros bb wlo whi aa Hin Hrr. vm_compute in Hin. destruct Hin.
        -- intros C. exfalso. exact (C T0).
    + exfalso. rewrite branch_eq_U, (U_atom E 17 ts E17), U_lit in Hc by lia.
      rewrite T0 in Hc. discriminate Hc.
  - (* ts <> 0 *)
    destruct (HTS T0) as (Hts8 & Hts4 & Hts47 & Hamr & Hra & Hwr).
    assert (HPR : forall a, ts <= a < ts + 8 -> apresent (w_H W3) (ms_mem ms3) a)
      by (intros a Ha; exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hwr a Ha)))).
    assert (HS : st_ok_pi SEGS VAL E ss_ts1 (restrict (w_H W3) ms3)).
    { rewrite Hms. unfold ss_ts1. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - apply Forall_cons; [|apply Forall_nil].
        unfold YP09.region_ok, R_ts. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U17. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). apply HPR. lia.
      - apply pairwise_disjoint_of_extents. cbn. repeat split.
      - split; [|split; [exact I | exact I]].
        cbn [ts_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U5, U17. unfold SB_TS. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
        repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
    assert (SHOK : sh_ok SEGS TBx ts_SH1 E (rdW W3 (ms_mem ms3))).
    { unfold sh_ok, ts_SH1. apply Forall_cons; [|apply Forall_nil].
      unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
      unfold TBx. rewrite (U_atom E 5 SB_TS E5) by (unfold SB_TS; lia).
      rewrite (U_atom E 17 ts E17) by lia. split.
      - rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of SEGS). exact Hra.
      - intros a Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SB_TS in *. cbn in Ha. lia. }
    clearbody E.
    paj_run_to_tok RUNTO HS HJ SHOK TSspan NP_exit.
    + unfold ss_ts1. cbn [ss_mem].
      eapply awr_ok_cons_gen; [reflexivity | exact U17 | | apply awr_ok_nil].
      unfold R_ts. cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply Hwr. lia.
    + eapply LAND; [exact HS | reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact HJ | | exact HG | ].
      * intros a Ha Hna. apply (kept_of_frame E _ (w_H W3) (ms_mem ms3) (ms_mem ms) (fun a => ts <> 0 /\ ts <= a < ts + 8) HFr);
          [| exact Ha | exact Hna].
        intros bb wlo whi aa Hin Hrr. vm_compute in Hin.
        repeat (destruct Hin as [Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U17 in Hrr;
                 first [lia | split; [exact T0 | lia]] |]).
        destruct Hin.
      * intros _.
        lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
          let r0 := eval vm_compute in (nth 0 (ss_mem ssx) R_ts) in
          pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W3) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
          cbn [ms_mem restrict mkst] in HR0 end.
        assert (Hs : 0 <= sec < 2 ^ 32) by (rewrite <- H18; apply Z.mod_pos_bound; lia).
        assert (Hu : 0 <= usec < 2 ^ 32) by (rewrite <- H24; apply Z.mod_pos_bound; lia).
        pose proof (field_of_region E _ 17 ts _ 0 8 0 8 0 8%N
          (SAlu ALU_ADD (SMd M_MULHU (SAlu ALU_SLL (SOff 18 0) (SLit 32)) (SLit 4294967296000000))
             (SAlu ALU_SRL (SAlu ALU_SLL (SOff 24 0) (SLit 32)) (SLit 32)))
          (sec * 1000000 + usec) HR0 U17
          ltac:(cbn; left; reflexivity)
          ltac:(rewrite denot_lit_U, U_tsv, E18, E24, H18, H24; reflexivity)
          ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
        rewrite Z.add_0_r in HV. exact HV.
Qed.


(* ---- the phase ---- *)

(* What the call kept of the caller's memory, after a run that wrote only bytes of E outside the image (Wr) and
   lost no byte. *)
Lemma ts_kept_after : forall lyc Sc (W : world SEGS) memc mdc (W3 : world SEGS) mem3 mem' sp (E Wr : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  nx_kept SEGS NX_STK_B B lyc Sc W memc W3 mem3 sp E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, Wr a -> E a) -> (forall a, in_img SEGS a -> ~ Wr a) ->
  mem_grows (rdW W3 mem3) (rdW W3 mem') ->
  nx_kept SEGS NX_STK_B B lyc Sc W memc W3 mem' sp E.
Proof.
  intros lyc Sc W memc mdc W3 mem3 mem' sp E Wr HAR (K1 & K2 & K3 & K4 & K5 & K6) HUN HWE HWI HG.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split.
  { intros a Ha Hw HnE. rewrite (HUN a ltac:(lia) ltac:(intros X; exact (HnE (HWE a X)))). exact (K1 a Ha Hw HnE). }
  split.
  { intros b m i Hb Hi HnE.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hceil & _).
    rewrite (HUN (b + i) ltac:(lia) ltac:(intros X; exact (HnE (HWE _ X)))). exact (K2 b m i Hb Hi HnE). }
  split.
  { intros a Hi Ho He. pose proof (pa_segs_low a Hi) as Hr2.
    rewrite (HUN a ltac:(lia) (HWI a Hi)). exact (K3 a Hi Ho He). }
  split.
  { intros cid pos a Hin Hr HnE.
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
    pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
    assert (Ha : 0 <= a < 2 ^ 64) by (unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; destruct Hr; lia).
    rewrite (HUN a Ha ltac:(intros X; exact (HnE (HWE _ X)))). exact (K4 cid pos a Hin Hr HnE). }
  split.
  { intros a Ha Hw Hp. apply (apresent_grows _ _ _ _ HG). exact (K5 a Ha Hw Hp). }
  intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (K6 a Ha).
Qed.

(* The stream's environment lies in the image (asource_img_laws, discharged once for the image). *)
Hypothesis ASIL : asource_img_laws SK SEGS B KS.

(* THE PHASE: from NP_ts with nx_ts_inv to NP_exit with nx_exit_inv. *)
Theorem pb_nx_ts : forall POST : ncx -> world SEGS -> config -> Prop,
  nx_from SK B KS POST (nx_exit_inv B MT KS) -> nx_from SK B KS POST (nx_ts_inv B MT KS).
Proof.
  intros POST HEX cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HTI.
  destruct HTI as (HM & Hfit & HBUF & R16 & R19 & R17 & R5 & R22 & R18 & R24).
  destruct HM as (HBD & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hq & _ & HTSm).
  destruct HBD as (HBD0 & HSL).
  destruct HBD0 as (Hpc & Hresv & Hpend & Hrom & Hfr & Hfcsr & HREGS & HSAV & HHDR & HFLW & HSH & Hlen & R25 & HFK).
  destruct HREGS as (R2 & R8 & R9 & R3 & R4).
  pose proof HB as (HJc & HROD & Hraw & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hal16 & Hwlo & Hwhi & Hch
    & Hroom & Hpsf & Hh64 & Hps8 & Hps4 & Hps47 & Hpsamr & Hpsown & Hpsf1 & Hpsf2 & HpsRA & HPS0 & Hsw & Hrng
    & HpsWR & HBUFB & HTSB & HSTR & HMETA & HE0 & HE02).
  clear Hpsamr.
  pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
  pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ as (HAR3 & Hly3 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK_B = 8464) by reflexivity.
  assert (Hsp : alloc_ceiling + NX_STK_B <= spZ (n_regs cx) <= 2 ^ 47) by lia.
  assert (Hsp1 : spZ (n_regs cx) - 272 <= n_sp1 cx <= spZ (n_regs cx) - 256).
  { pose proof (proj1 (NX_STK_B_frame _ Hal16)) as X. unfold NX_MFRAME in X. unfold n_sp1. lia. }
  (* this call's frame, as the layouts see it *)
  assert (EFA : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
  { intros c p. unfold frame_addr.
    destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _). destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _).
    rewrite EF3, EFc. reflexivity. }
  assert (HFB : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity).
  assert (HinF : In (NX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp HAR3 HinF) as (HF4096 & HFceil & _).
  rewrite EFA in HF4096, HFceil. rewrite HFB in HFceil.
  change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in HF4096, HFceil.
  assert (HSHa : nSH cx fp = SHADOW_OFF + nF cx fp / 8) by reflexivity.
  (* lia sees divisions as atoms here (lib/A/Prog/YC4b.v sets zify's euclidean-division flag to false) *)
  pose proof (Z.div_mod (nF cx fp) 8 ltac:(lia)) as HD8.
  pose proof (Z.mod_pos_bound (nF cx fp) 8 ltac:(lia)) as HM8.
  (* where the timestamp cell is: in a frame of the caller, apart from everything the exit reads *)
  assert (TAP : n_ts cx <> 0 -> forall a, n_ts cx <= a < n_ts cx + 8 ->
     0 <= a < 2 ^ 64 /\
     ~ (spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx)) /\
     ~ (nF cx fp <= a < nF cx fp + 64) /\ ~ (nSH cx fp <= a < nSH cx fp + 8) /\
     ~ (n_ps cx <= a < n_ps cx + PS_LEN) /\ ~ (n_buf cx <= a < n_buf cx + nx_bufn (n_cap cx)) /\
     ~ (n_h cx <= a < n_h cx + SRC_FILE_BLOCK) /\ ~ (n_b cx <= a < n_b cx + Z.of_nat (length (n_C cx))) /\
     ~ in_img SEGS a).
  { intros T0 a Ha.
    destruct (HTSB Hh T0) as (_ & Hts8 & Hts4 & Hts47 & Hamr & (tcid & tpos & Htin & Ht1 & Ht2) & HtsWR & _ & Htps & Htbuf).
    destruct (HSTR Hh) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htsr & _).
    destruct (Htsr T0) as (Hth & Htb).
    assert (Htin' : In (tcid, tpos) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Htin).
    destruct (in_split _ _ Htin') as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (NX_CID, fp) (tcid, tpos) [] l2 l3 HAR3
      ltac:(rewrite HFR, El; reflexivity)) as Dff.
    unfold zdisjoint, frame_rng in Dff. cbn [fst snd] in Dff. rewrite !EFA, HFB in Dff.
    change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in Dff.
    pose proof (frm_off_imgP B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) tcid tpos HARc Htin') as Hoff.
    unfold off_img in Hoff.
    (* each fact from its own premises only: lia over the whole context splits on every disjunction *)
    split; [clear - Ha Hts4 Hts47; lia|].
    split; [intros Hw; exact (proj2 (HtsWR a Ha) Hw)|].
    split; [clear - Ha Dff Ht1 Ht2; lia|].
    split; [rewrite HSHa; clear - Ha Hamr HF4096 HFceil C1 HD8 HM8;
            unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *; lia|].
    split; [clear - Ha Htps; unfold PS_LEN in *; lia|].
    split; [clear - Ha Htbuf; lia|]. split; [clear - Ha Hth; lia|]. split; [clear - Ha Htb; lia|].
    intros Hi. pose proof (pa_img_range a Hi) as Hr. clear - Ha Hr Hoff Ht1 Ht2.
    unfold off_img, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia. }
  apply (ts_run W3 ms3 md3 (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
           ((NX_CID, fp) :: n_own cx) ly3 S3 k2 (n_ts cx)
           (nx_tsec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx)) (nx_tusec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx))
           (nx_reclen (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx)) (POST cx)
           HJ Hpc Hresv Hpend Hrom Hfr Hfcsr R5 R17 R22 R18 R24).
  - (* the timestamp cell, for the run *)
    intros T0.
    destruct (HTSB Hh T0) as (_ & Hts8 & Hts4 & Hts47 & Hamr & (tcid & tpos & Htin & Ht1 & Ht2) & HtsWR & _ & _ & _).
    destruct (HTSm T0) as (_ & HtsRA).
    split; [exact Hts8|]. split; [exact Hts4|]. split; [exact Hts47|]. split; [exact Hamr|]. split; [exact HtsRA|].
    intros a Ha. right; right; right. unfold in_frames. exists tcid, tpos. split; [right; exact Htin|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. lia.
  - (* NP_exit: nx_exit_inv *)
    intros ms' md' HJ' (Hsh & KEEPR & R11 & HUN & HG & HV & Hfd & Hfs).
    apply (HEX cx fp k2 ly3 S3 W3 ms' md' HB HJ' HFR).
    assert (KW : forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) ->
      aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply HUN; [lia|]. intros [T0 Hx]. destruct (TAP T0 a Hx) as (_ & Hw & _). exact (Hw Ha). }
    assert (KF : forall a, nF cx fp <= a < nF cx fp + 64 ->
      aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply HUN; [lia|]. intros [T0 Hx]. destruct (TAP T0 a Hx) as (_ & _ & Hf & _). exact (Hf Ha). }
    assert (KSH : forall a, nSH cx fp <= a < nSH cx fp + 8 ->
      aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply HUN; [rewrite HSHa in Ha; unfold SHADOW_OFF in Ha; lia|].
      intros [T0 Hx]. destruct (TAP T0 a Hx) as (_ & _ & _ & Hs & _). exact (Hs Ha). }
    (* the slots: all at s1 + 24 .. s1 + 128, inside this call's window *)
    assert (SLK : forall off v, 0 <= off <= 120 ->
      rdword (aview SEGS (w_H W3) (ms_mem ms3)) (n_sp1 cx + off) = Some v ->
      rdword (aview SEGS (w_H W3) (ms_mem ms')) (n_sp1 cx + off) = Some v).
    { intros off v Hoff Hr. apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KW; lia | exact Hr]. }
    unfold nx_exit_inv. split; [split|].
    + (* nx_body0 at NP_exit *)
      unfold nx_body0.
      split; [rewrite Hsh; reflexivity|]. split; [rewrite Hsh; reflexivity|].
      split; [rewrite Hsh; reflexivity|]. split; [rewrite Hsh; reflexivity|].
      split; [rewrite Hsh; reflexivity|]. split; [rewrite Hsh; reflexivity|].
      split.
      { unfold nregs. split; [rewrite KEEPR by inkeep; exact R2|]. split; [rewrite KEEPR by inkeep; exact R8|].
        split; [rewrite KEEPR by inkeep; exact R9|]. split; [rewrite KEEPR by inkeep; exact R3|].
        rewrite KEEPR by inkeep; exact R4. }
      split.
      { destruct HSAV as (SV1 & SV2). split.
        - apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KW; lia | exact SV1].
        - intros j Hj. apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KW; lia | exact (SV2 j Hj)]. }
      split.
      { destruct HHDR as (HD1 & HD2 & HD3). split; [|split].
        - apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KF; lia | exact HD1].
        - apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KF; lia | exact HD2].
        - apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KF; lia | exact HD3]. }
      split.
      { unfold nflagw in *. apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KF; unfold NX_FLAGPTR; lia | exact HFLW]. }
      split.
      { intros i Hi. assert (Hi8 : Z.of_nat i < 8) by (rewrite Hlen in Hi; unfold NX_NSH in Hi; lia).
        rewrite (KSH (nSH cx fp + Z.of_nat i)) by lia. exact (HSH i Hi). }
      split; [exact Hlen|].
      split; [rewrite KEEPR by inkeep; exact R25|].
      unfold nslot in *. apply SLK; [unfold NS_FK; lia | exact HFK].
    + (* the spill slots *)
      destruct HSL as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8' & S9 & S10 & S11 & S12).
      unfold nslots, nslot in *.
      split; [apply SLK; [unfold NS_FK; lia | exact S1]|].
      split; [apply SLK; [unfold NS_F0; lia | exact S2]|].
      split; [apply SLK; [unfold NS_BUF; lia | exact S3']|].
      split; [apply SLK; [unfold NS_TS; lia | exact S4]|].
      split; [apply SLK; [unfold NS_SB; lia | exact S5]|].
      split; [apply SLK; [unfold NS_PS12; lia | exact S6]|].
      split; [apply SLK; [unfold NS_SH12; lia | exact S7]|].
      split; [apply SLK; [unfold NS_OFF8; lia | exact S8']|].
      split; [apply SLK; [unfold NS_OFF12; lia | exact S9]|].
      split; [apply SLK; [unfold NS_PH4; lia | exact S10]|].
      split; [apply SLK; [unfold NS_PH8; lia | exact S11]|].
      apply SLK; [unfold NS_PH12; lia | exact S12].
    + split; [rewrite KEEPR by inkeep; exact R19|].
      split; [rewrite KEEPR by inkeep; exact R16|].
      split.
      { (* the journal's bookkeeping *)
        destruct HJBK as (Hk2 & Hab & Hmo & Hfd0 & Hfs0).
        split; [exact Hk2|]. split; [exact Hab|]. split; [exact Hmo|].
        split; [rewrite Hfd; exact Hfd0 | rewrite Hfs; exact Hfs0]. }
      (* the caller's memory and the result *)
      unfold nx_fin_at, nx_fin. right.
      destruct (HSTR Hh) as (Hinh & Hinb & _ & _ & _ & _ & _ & _ & _ & _ & _).
      destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hinh)
        as (_ & Hh4096 & Hhceil & _).
      destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hinb)
        as (_ & Hb4096 & Hbceil & _).
      change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
      pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as [_ Hreqb].
      split; [exact Hh|].
      split; [rewrite R11, (nx_res_fit _ _ _ _ Hfit); reflexivity|].
      split.
      { change (nx_wrset (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx)) with (nx_E cx).
        apply (ts_kept_after (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) W3 (ms_mem ms3) (ms_mem ms')
                 (spZ (n_regs cx)) (nx_E cx) (fun a => n_ts cx <> 0 /\ n_ts cx <= a < n_ts cx + 8) HARc HKEPT HUN).
        - intros a [T0 Ha]. unfold nx_E, nx_wrset. right; right; left. split; [exact T0 | exact Ha].
        - intros a Hi [T0 Ha]. destruct (TAP T0 a Ha) as (_ & _ & _ & _ & _ & _ & _ & _ & Hni). exact (Hni Hi).
        - exact HG. }
      split.
      { apply (PcapSourceCloseSpec.asource_at_frame_segs _ KS (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms'))); [|exact HSRC].
        intros a Ha. apply (mbyte_of_aview SEGS).
        assert (Har : 0 <= a < 2 ^ 64).
        { destruct Ha as [Ha | [Ha | Ha]]; [unfold SRC_FILE_BLOCK in *; lia | lia |].
          pose proof (pa_segs_low a (proj1 (asil_env _ _ _ _ ASIL a Ha))). lia. }
        apply HUN; [exact Har|]. intros [T0 Hx].
        destruct (TAP T0 a Hx) as (_ & _ & _ & _ & _ & _ & Hth & Htb & Hni).
        destruct Ha as [Ha | [Ha | Ha]];
          [exact (Hth Ha) | exact (Htb Ha) | exact (Hni (proj1 (asil_env _ _ _ _ ASIL a Ha)))]. }
      split.
      { apply (ts_ps_keep W3 (ms_mem ms3)); [|exact HPS].
        intros x Hx. apply HUN; [clear - Hx Hps4 Hps47; unfold PS_LEN in *; lia|]. intros [T0 Hy].
        destruct (TAP T0 x Hy) as (_ & _ & _ & _ & Hp & _). exact (Hp Hx). }
      split.
      { destruct HBUF as (bj' & Hg & Hlb & Hpre).
        destruct (HBUFB Hh) as (_ & Hbuf4 & Hbuf63 & _ & Hlbj & _).
        exists bj'. split; [|split; [exact Hlb | intros _; exact Hpre]].
        apply (ts_garr8_keep W3 (ms_mem ms3)); [|exact Hg].
        intros x Hx. rewrite Hlb, Hlbj in Hx. apply HUN; [unfold nx_bufn in *; lia|]. intros [T0 Hy].
        destruct (TAP T0 x Hy) as (_ & _ & _ & _ & _ & Hbf & _). exact (Hbf Hx). }
      intros T0. rewrite (nx_tsv_fit _ _ _ _ _ Hfit). exact (HV T0).
Qed.

(* The phase in the shape the top takes it (lib/B/Prog/PcapSourceNext.v, H_fitB). *)
Corollary pb_nx_tsX :
  nx_from SK B KS (nx_post SK B MT KS) (nx_exit_inv B MT KS) -> nx_from SK B KS (nx_post SK B MT KS) (nx_ts_inv B MT KS).
Proof. exact (pb_nx_ts (nx_post SK B MT KS)). Qed.

End c.
End b.
End a.

(* SK is explicit at every use (as lib/B's PcapSourceNextDefs): the closure's only global sink_head
   instance is the PLAIN build's (lib/Reusable/YI5b.v:12), so an inferred SK would make the stream facts vacuous. *)
Arguments pb_nx_ts {fx rc} SK {PI}.
Arguments pb_nx_tsX {fx rc} SK {PI}.

(* GUARD: SK is passed by position; were it implicit again, this line would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) (B : asyms)
  (MT : ameter_ops) (KS : asource_syms) (LAWS : AR_laws pa_segs B) (ASIL : asource_img_laws SK pa_segs B KS) =>
  pb_nx_tsX (fx:=fx) (rc:=rc) SK (PI:=PI) B MT KS LAWS ASIL).
