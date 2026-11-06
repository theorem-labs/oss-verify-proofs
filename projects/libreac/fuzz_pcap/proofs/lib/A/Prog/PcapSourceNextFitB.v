(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 491 of its 546 lines of code are new or changed and 876 lines of the source are left out. *)
(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the walk of the phase NP_ts
   (listing offset 0x15ac, address 0x81ce4) to NP_exit (0x15ec, 0x81d24). The phase stores the
   record's timestamp into the caller's cell when the caller asked for one, and sets the word the
   call returns. Its entry predicate is nx_ts_inv (PcapSourceNextFitBDefs.v).

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...; symbols from its unstripped twin, capstone 5 disassembly).

   THE RUN (ts_run, at the machine level). The engine (PcapPaLib.paj_run_to) walks the slots
   0x81ce4 .. 0x81d20 from a symbolic state whose registers are the atoms of the machine registers
   (sr_atoms) and whose memory is:
   - R_sb: the spill slot NS_SB at s1 + 40, which holds the shadow base 0x7fff8000 (atom 32); the
     check reloads the base from it (`ld a1,0x28(s1)` 0x81cec);
   - R_ts: the caller's 8-byte cell at s5 = ts (atom 21), writable; only when ts <> 0.
   ts <> 0: the atom facts 4096 <= ts <= 2^47 - 8, ts mod 8 = 0 decide `beqz s5` (0x81ce4) and,
   through the shadow entry (21, 0, 8), the shadow check of ts (0x81ce8 .. 0x81cf8: `bnez a0` to
   the error path 0x81e88 is not taken, the shadow byte of ts is 0 by range_addressable). ts = 0: the
   engine leaves `beqz s5` open; its fall-through arm contradicts s5 = 0, its taken arm runs
   0x81d1c .. 0x81d20. The run stops at NP_exit with
     a0 = mulhu (s10 << 32) (10^6 << 32) + ((s7 << 32) >> 32) stored at ts (ts <> 0 only),
     s6 = (s9 << 32) >> 32,
   and s7, s9, s10, a1 changed; every other register is the one it started with.
   (0x3d09 << 38 = 15625 * 2^38 = 10^6 * 2^32, so mulhu gives sec * 10^6 for a 32-bit sec.)

   WHY THE SEAT IS LOCAL. ts_run seats its own 2-region symbolic state instead of the shared seat
   PcapSourceNextSeat.nx_seat / nx_land_by: it was written before a Theorem Labs lane's file landed, and it serves
   only this 17-slot run, which reads one spill slot and writes one caller cell. It is private to this
   phase (nothing else uses it); the landing to nx_body is done from ts_after's frame facts below.

   THE PHASE (pb_nx_ts). The caller's cell lies in a frame of the caller's own (nx_base), so it is
   apart from this call's machine frame (nx_wr_ok), from its side-stack frame and that frame's
   shadow (sep_frames_pos, amem_range), from ps, buf, the stream's FILE block and data (nx_base) and
   from the image (frm_off_imgP). Every fact of nx_exit_inv that nx_ts_inv states over other bytes is
   therefore kept; the store adds the model's timestamp (PSN.rec_ts) and s6 the model's result. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceMeter PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceNextFitBDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state of the phase ---- *)

Definition SB_TS : Z := 0x7fff8000.        (* the shadow base, SHADOW_OFF *)
Definition TBx : sv := SOff 32 0.          (* the atom that holds it *)
Definition TSspan : Z * Z := (SB_TS, SB_TS + 2 ^ 44 - 1).
(* The spill slot NS_SB (40) above s1, read-only, holding the shadow base. *)
Definition R_sb : YP09.region := YP09.mkRegion (Some 9%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
(* The caller's timestamp cell at s5, writable. *)
Definition R_ts : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 8 [].
Definition ts_SH1 : list shent := [mkSHE 21 0 8].
Definition ts_facts1 : facts := mkFacts [(21%nat, mkAF 4096 (2 ^ 47 - 8) 3); (32%nat, mkAF SB_TS SB_TS 0)] [] [].
Definition ss_ts1 : sstate := mkSS NP_ts sr_atoms [R_sb; R_ts] None ts_facts1.
Definition ts_facts0 : facts := mkFacts [(21%nat, mkAF 0 0 0); (32%nat, mkAF SB_TS SB_TS 0)] [] [].
Definition ss_ts0 : sstate := mkSS NP_ts sr_atoms [] None ts_facts0.
Definition ts_extra : list word := [Z_to_bv 64 SB_TS].
(* The registers the phase does not write: all but a0, a1, s6, s7, s9 and s10. *)
Definition NX_TS_KEEP : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 24; 27; 28; 29; 30; 31]%bv.

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

(* (x << 32) >> 32: the low word of x (0x81d10, 0x81d1c..0x81d20). *)
Lemma U_lo32 : forall E n,
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 32)) = bv_unsigned (ew E n) mod 2 ^ 32.
Proof.
  intros E n. rewrite U_SAlu, U_hi32, U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 32) 63) with 32.
  pose proof (Z.mod_pos_bound (bv_unsigned (ew E n)) (2 ^ 32) ltac:(lia)) as Hm.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
  apply zcanon_id. unfold M64. lia.
Qed.

(* The stored timestamp (0x81cfc..0x81d14): mulhu (sec << 32) (10^6 << 32) + usec = sec * 10^6 + usec,
   for the low words sec of s10 and usec of s7. *)
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

(* The realigned stack pointer s1 lies 224 to 255 bytes below the entry sp (0x8181c, 0x8185c). *)
Lemma nx_sp1_range : forall sp, sp - 256 < nx_sp1 sp <= sp - 224.
Proof.
  intros sp. unfold nx_sp1, NX_MFRAME.
  pose proof (Z.div_mod (sp - 224) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp - 224) 32 ltac:(lia)). lia.
Qed.

(* A register of the list NX_TS_KEEP. *)
Ltac inkeep := unfold NX_TS_KEEP; cbn [In]; repeat (first [left; reflexivity | right]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

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
  unfold nx_ps_at. unfold PS_LEN, PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
  split; [eapply ts_vm_keep; [|exact P1]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply ts_vm_keep; [|exact P2]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply ts_vm_keep; [|exact P3]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply ts_vm_keep; [|exact P4]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply ts_vm_keep; [|exact P5]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply ts_garr8_keep; [|exact P6]; intros x Hx; apply K; rewrite P7 in Hx; cbn in Hx; lia|].
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
  getr (ms_regs ms') 22 = w64 len /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ts <> 0 /\ ts <= a < ts + 8) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) /\
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) /\
  (ts <> 0 -> val_mem SEGS (rdW W3 (ms_mem ms')) ts 8 (sec * 1000000 + usec)) /\
  m_fds md' = m_fds md3 /\ m_fs md' = m_fs md3.

(* The run of the phase, at the machine level. *)
Lemma ts_run : forall (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2
  (sp1 ts sec usec len : Z) (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  ms_pc_val ms3 = w64 (BASE + NP_ts) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 9 = w64 sp1 -> 0 <= sp1 -> sp1 + 48 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + NS_SB) = Some SHADOW_OFF ->
  getr (ms_regs ms3) 21 = w64 ts ->
  bv_unsigned (getr (ms_regs ms3) 25) mod 2 ^ 32 = len ->
  bv_unsigned (getr (ms_regs ms3) 26) mod 2 ^ 32 = sec ->
  bv_unsigned (getr (ms_regs ms3) 23) mod 2 ^ 32 = usec ->
  (ts <> 0 ->
     ts mod 8 = 0 /\ 4096 <= ts /\ ts + 8 <= 2 ^ 47 /\ amem_range ts 8 /\
     range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF ts 8 /\
     (forall a, ts <= a < ts + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly3 S3) ly3 own a) /\
     (ts + 8 <= sp1 + NS_SB \/ sp1 + NS_SB + 8 <= ts)) ->
  (forall ms' md',
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms') md' k2 ->
     ts_after W3 ms3 ms' md3 md' ts sec usec len ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros W3 ms3 md3 STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 sp1 ts sec usec len Q
    HJ Hpc Hresv Hpend Hrom Hfr Hfcsr H9 Hsp0 Hsp1 Hsb H21 H25 H26 H23 HTS HK.
  unfold NS_SB in *.
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + NP_ts)) (rdW W3 (ms_mem ms3)) (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0' rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfr, Hfcsr.
    subst. reflexivity. }
  assert (Hts64 : 0 <= ts < 2 ^ 64).
  { destruct (Z.eq_dec ts 0) as [->|T]; [lia|]. destruct (HTS T) as (_ & Hts4 & Hts47 & _). lia. }
  set (E := Eimg (Ereg (ms_regs ms3) ts_extra)).
  assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) ts_extra) n)
    by (intros n Hn; apply Eimg_low; exact Hn).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) ts_extra) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 sp1)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 9 9%bv eq_refl); exact H9).
  assert (E21 : ew E 21 = Z_to_bv 64 ts)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 21 21%bv eq_refl); exact H21).
  assert (E23 : ew E 23 = getr (ms_regs ms3) 23)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
  assert (E25 : ew E 25 = getr (ms_regs ms3) 25)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 25 25%bv eq_refl)).
  assert (E26 : ew E 26 = getr (ms_regs ms3) 26)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_TS)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = ts) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SB_TS) by (rewrite E32; apply unsigned_lit_small; unfold SB_TS; lia).
  (* The landing: the same for both arms. *)
  assert (LAND : forall ss (ms : machine_state) mat,
    st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = NP_exit ->
    forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) NX_TS_KEEP = true ->
    sr_get (ss_regs ss) 22 = SAlu ALU_SRL (SAlu ALU_SLL (SOff 25 0) (SLit 32)) (SLit 32) ->
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k2 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (ts <> 0 /\ ts <= a < ts + 8) ->
       aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
    mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms)) ->
    (ts <> 0 -> val_mem SEGS (rdW W3 (ms_mem ms)) ts 8 (sec * 1000000 + usec)) ->
    SRr SEGS W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q).
  { intros ss ms mat HS Hrv Hpc' Hkeep Hr22 HJ' HUN HG' HV.
    apply (HK ms _ HJ'). unfold ts_after.
    split.
    { pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hsh. rewrite Hpc' in Hsh. exact Hsh. }
    split.
    { intros r Hr. pose proof (regs_kept_of_st_ok_pi E ss _ (ms_regs ms3) ts_extra NX_TS_KEEP HS HAE Hkeep r Hr) as Hk.
      cbn [restrict ms_regs] in Hk. exact Hk. }
    split.
    { pose proof (st_ok_pi_restrict_reg (w_H W3) E ss ms 22%bv HS) as R22. rewrite Hr22 in R22.
      rewrite R22, denot_lit_U, U_lo32, E25, H25. reflexivity. }
    split; [exact HUN|]. split; [exact HG'|]. split; [exact HV|].
    destruct md3. split; reflexivity. }
  destruct (Z.eq_dec ts 0) as [T0 | T0].
  - (* ts = 0: `beqz s5` is taken, no store *)
    assert (HS : st_ok_pi SEGS VAL E ss_ts0 (restrict (w_H W3) ms3)).
    { rewrite Hms. unfold ss_ts0. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - apply Forall_nil.
      - apply pairwise_disjoint_of_extents. cbn. exact I.
      - split; [|split; [exact I | exact I]].
        cbn [ts_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U21, U32, T0. unfold SB_TS.
        repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia]. }
    assert (SHOK : sh_ok SEGS TBx [] E (rdW W3 (ms_mem ms3))) by (unfold sh_ok; apply Forall_nil).
    clearbody E.
    (* the engine leaves `beqz s5` (0x81ce4) open for ts = 0: take both arms *)
    psrr_branch_tok RUNTO BR HS SHOK TSspan.
    + (* taken: 0x81d1c .. 0x81d20 *)
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK TSspan NP_exit.
      * lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
          let rs' := eval vm_compute in rs in change rs with rs' end.
        apply awr_ok_nil.
      * eapply LAND; [exact HS | reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact HJ | | exact HG | ].
        -- intros a Ha Hna. apply (kept_of_frame E _ (w_H W3) (ms_mem ms3) (ms_mem ms) (fun _ => False) HFr);
             [| exact Ha | intros []].
           intros bb wlo whi aa Hin Hrr. vm_compute in Hin. destruct Hin.
        -- intros C. exfalso. exact (C T0).
    + (* not taken: s5 = ts = 0 *)
      exfalso. rewrite branch_eq_U, (U_atom E 21 ts E21), U_lit in Hc by lia.
      rewrite T0 in Hc. discriminate Hc.
  - (* ts <> 0: the shadow check of ts and the store *)
    destruct (HTS T0) as (Hts8 & Hts4 & Hts47 & Hamr & Hra & Hwr & Hdj).
    assert (HPR : forall a, ts <= a < ts + 8 -> apresent (w_H W3) (ms_mem ms3) a)
      by (intros a Ha; exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hwr a Ha)))).
    assert (HS : st_ok_pi SEGS VAL E ss_ts1 (restrict (w_H W3) ms3)).
    { rewrite Hms. unfold ss_ts1. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        + unfold YP09.region_ok, R_sb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
          rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff 32 0) SB_TS).
          * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
          * unfold SB_TS. cbn. lia.
          * cbn. lia.
          * apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hsb.
        + unfold YP09.region_ok, R_ts. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
          rewrite U21. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
          intros o Ho. apply (apresent_writable SEGS). apply HPR. lia.
      - apply pairwise_disjoint_of_extents. unfold extent_of_region.
        cbn [map R_sb R_ts YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U21.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
      - split; [|split; [exact I | exact I]].
        cbn [ts_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U21, U32. unfold SB_TS. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
        repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
    assert (SHOK : sh_ok SEGS TBx ts_SH1 E (rdW W3 (ms_mem ms3))).
    { unfold sh_ok, ts_SH1. apply Forall_cons; [|apply Forall_nil].
      unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
      unfold TBx. rewrite (U_atom E 32 SB_TS E32) by (unfold SB_TS; lia).
      rewrite (U_atom E 21 ts E21) by lia. split.
      - rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of SEGS). exact Hra.
      - intros a Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SB_TS in *. cbn in Ha. lia. }
    clearbody E.
    paj_run_to_tok RUNTO HS HJ SHOK TSspan NP_exit.
    + unfold ss_ts1. cbn [ss_mem]. apply awr_ok_cons_ro; [unfold R_sb; cbn; lia|].
      eapply awr_ok_cons_gen; [reflexivity | exact U21 | | apply awr_ok_nil].
      unfold R_ts. cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply Hwr. lia.
    + eapply LAND; [exact HS | reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact HJ | | exact HG | ].
      * intros a Ha Hna. apply (kept_of_frame E _ (w_H W3) (ms_mem ms3) (ms_mem ms) (fun a => ts <> 0 /\ ts <= a < ts + 8) HFr);
          [| exact Ha | exact Hna].
        intros bb wlo whi aa Hin Hrr. vm_compute in Hin.
        repeat (destruct Hin as [Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U21 in Hrr;
                 first [lia | split; [exact T0 | lia]] |]).
        destruct Hin.
      * intros _.
        lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
          let r1 := eval vm_compute in (nth 1 (ss_mem ssx) R_sb) in
          pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W3) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
          cbn [ms_mem restrict mkst] in HR1 end.
        assert (Hs : 0 <= sec < 2 ^ 32) by (rewrite <- H26; apply Z.mod_pos_bound; lia).
        assert (Hu : 0 <= usec < 2 ^ 32) by (rewrite <- H23; apply Z.mod_pos_bound; lia).
        pose proof (field_of_region E _ 21 ts _ 0 8 0 8 0 8%N
          (SAlu ALU_ADD (SMd M_MULHU (SAlu ALU_SLL (SOff 26 0) (SLit 32)) (SLit 4294967296000000))
             (SAlu ALU_SRL (SAlu ALU_SLL (SOff 23 0) (SLit 32)) (SLit 32)))
          (sec * 1000000 + usec) HR1 U21
          ltac:(cbn; left; reflexivity)
          ltac:(rewrite denot_lit_U, U_tsv, E26, E23, H26, H23; reflexivity)
          ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
        rewrite Z.add_0_r in HV. exact HV.
Qed.

(* ---- the phase ---- *)

(* What the call kept of the caller's memory, after a run that wrote only bytes of E outside the
   image (Wr) and lost no byte. *)
Lemma ts_kept_after : forall lyc Sc (W : world SEGS) memc mdc (W3 : world SEGS) mem3 mem' sp (E Wr : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  nx_kept SEGS NX_STK B lyc Sc W memc W3 mem3 sp E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, Wr a -> E a) -> (forall a, in_img SEGS a -> ~ Wr a) ->
  mem_grows (rdW W3 mem3) (rdW W3 mem') ->
  nx_kept SEGS NX_STK B lyc Sc W memc W3 mem' sp E.
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
  destruct HTI as (HM & Hfit & HBUF & R21 & R25 & R26 & R23).
  destruct HM as (HBD & R24 & HJBK & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hq & _ & HTSm).
  destruct HBD as (HBD0 & HSL).
  destruct HBD0 as (Hpc & Hresv & Hpend & Hrom & Hfr & Hfcsr & HREGS & HSAV & HHDR & HFLW & HSH & Hlen
                    & R18 & R19 & HF0).
  destruct HREGS as (R2 & R8 & R9 & R3 & R4).
  pose proof HB as (HJc & HROD & Hraw & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hal16 & Hwlo & Hwhi & Hch
    & Hroom & Hpsf & Hh64 & Hps8 & Hps4 & Hps47 & Hpsamr & Hpsown & Hpsf1 & Hpsf2 & HpsRA & HPS0 & Hsw & Hrng
    & HpsWR & HBUFB & HTSB & HSTR & HMETA & HE0 & HE02).
  pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
  pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ as (HAR3 & Hly3 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK = 8496) by reflexivity.
  assert (Hsp : alloc_ceiling + NX_STK <= spZ (n_regs cx) <= 2 ^ 47)
    by (clear - Hceil Hslo Hshi H47 Hwlo Hwhi; lia).
  assert (Hsp1 : spZ (n_regs cx) - 256 < n_sp1 cx <= spZ (n_regs cx) - 224) by (unfold n_sp1; apply nx_sp1_range).
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
  (* the frame's shadow address, without a division in the arithmetic below *)
  assert (HD8 : 512 <= nF cx fp / 8 <= 0xFFFFFFF0000).
  { clear - HF4096 HFceil C1. split.
    - apply Z.div_le_lower_bound; lia.
    - apply Z.div_le_upper_bound; lia. }
  assert (HSHr : SHADOW_OFF + 512 <= nSH cx fp <= SHADOW_OFF + 0xFFFFFFF0000)
    by (rewrite HSHa; clear - HD8; lia).
  clear HSHa.
  (* where the timestamp cell is: in a frame of the caller, apart from everything the exit reads *)
  assert (TAP : n_ts cx <> 0 -> forall a, n_ts cx <= a < n_ts cx + 8 ->
     0 <= a < 2 ^ 64 /\
     ~ (spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx)) /\
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
    split; [clear - Ha Hts4 Hts47; lia|].
    split; [intros Hw; exact (proj2 (HtsWR a Ha) Hw)|].
    split; [clear - Ha Ht1 Ht2 Dff; lia|].
    split; [clear - Ha Hamr HSHr; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *; lia|].
    split; [clear - Ha Htps; unfold PS_LEN in *; lia|].
    split; [clear - Ha Htbuf; lia|]. split; [clear - Ha Hth; lia|]. split; [clear - Ha Htb; lia|].
    intros Hi. pose proof (pa_img_range a Hi) as Hr. clear - Ha Ht1 Ht2 Hoff Hr.
    unfold pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia. }
  apply (ts_run W3 ms3 md3 (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
           ((NX_CID, fp) :: n_own cx) ly3 S3 k2 (n_sp1 cx) (n_ts cx)
           (nx_tsec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx)) (nx_tusec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx))
           (nx_reclen (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx)) (POST cx)
           HJ Hpc Hresv Hpend Hrom Hfr Hfcsr R9 ltac:(clear - Hsp Hsp1 C1 HNX; lia) ltac:(clear - Hsp Hsp1; lia)
           (proj1 (proj2 (proj2 (proj2 HSL))))
           R21 R25 R26 R23).
  - (* the timestamp cell, for the run *)
    intros T0.
    destruct (HTSB Hh T0) as (_ & Hts8 & Hts4 & Hts47 & Hamr & (tcid & tpos & Htin & Ht1 & Ht2) & HtsWR & _ & _ & _).
    destruct (HTSm T0) as (_ & HtsRA).
    split; [exact Hts8|]. split; [exact Hts4|]. split; [exact Hts47|]. split; [exact Hamr|]. split; [exact HtsRA|].
    split.
    + intros a Ha. right; right; right. unfold in_frames. exists tcid, tpos. split; [right; exact Htin|].
      left. unfold in_zr. cbn [fst snd]. rewrite EFA. clear - Ha Ht1 Ht2. lia.
    + unfold NS_SB.
      pose proof (proj2 (HtsWR (n_ts cx) ltac:(clear; lia))) as Hw0.
      pose proof (proj2 (HtsWR (n_ts cx + 7) ltac:(clear; lia))) as Hw7.
      clear - Hw0 Hw7 Hsp1 HNX. lia.
  - (* NP_exit: nx_exit_inv *)
    intros ms' md' HJ' (Hsh & KEEPR & R22 & HUN & HG & HV & Hfd & Hfs).
    apply (HEX cx fp k2 ly3 S3 W3 ms' md' HB HJ' HFR).
    assert (KW : forall a, spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx) ->
      aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply HUN; [clear - Ha Hsp HNX C1; lia|].
      intros [T0 Hx]. destruct (TAP T0 a Hx) as (_ & Hw & _). exact (Hw Ha). }
    assert (KF : forall a, nF cx fp <= a < nF cx fp + 64 ->
      aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply HUN; [clear - Ha HF4096 HFceil C1; lia|].
      intros [T0 Hx]. destruct (TAP T0 a Hx) as (_ & _ & Hf & _). exact (Hf Ha). }
    assert (KSH : forall a, nSH cx fp <= a < nSH cx fp + 8 ->
      aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply HUN; [clear - Ha HSHr; unfold SHADOW_OFF in *; lia|].
      intros [T0 Hx]. destruct (TAP T0 a Hx) as (_ & _ & _ & Hs & _). exact (Hs Ha). }
    unfold nx_exit_inv. split; [split|split].
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
        - apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KW; clear - Hi HNX; lia | exact SV1].
        - intros j Hj. apply (ts_rdword_keep W3 (ms_mem ms3));
            [intros i Hi; apply KW; clear - Hi Hj HNX; lia | exact (SV2 j Hj)]. }
      split.
      { destruct HHDR as (HD1 & HD2 & HD3). split; [|split].
        - apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KF; clear - Hi; lia | exact HD1].
        - apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KF; clear - Hi; lia | exact HD2].
        - apply (ts_rdword_keep W3 (ms_mem ms3)); [intros i Hi; apply KF; clear - Hi; lia | exact HD3]. }
      split.
      { unfold nflagw in *. apply (ts_rdword_keep W3 (ms_mem ms3));
          [intros i Hi; apply KF; unfold NX_FLAGPTR; clear - Hi; lia | exact HFLW]. }
      split.
      { intros i Hi. assert (Hi8 : Z.of_nat i < 8) by (rewrite Hlen in Hi; unfold NX_NSH in Hi; clear - Hi; lia).
        rewrite (KSH (nSH cx fp + Z.of_nat i)) by (clear - Hi8; lia). exact (HSH i Hi). }
      split; [exact Hlen|].
      split; [rewrite KEEPR by inkeep; exact R18|].
      split; [rewrite KEEPR by inkeep; exact R19|].
      unfold nslot in *. apply (ts_rdword_keep W3 (ms_mem ms3));
        [intros i Hi; apply KW; unfold NS_F0; clear - Hi Hsp1 HNX; lia | exact HF0].
    + (* the spill slots: all at s1 + 16 .. s1 + 120, inside this call's window *)
      assert (SLK : forall off v, 0 <= off <= 112 ->
        rdword (aview SEGS (w_H W3) (ms_mem ms3)) (n_sp1 cx + off) = Some v ->
        rdword (aview SEGS (w_H W3) (ms_mem ms')) (n_sp1 cx + off) = Some v).
      { intros off v Hoff Hr. apply (ts_rdword_keep W3 (ms_mem ms3));
          [intros i Hi; apply KW; clear - Hi Hoff Hsp1 HNX; lia | exact Hr]. }
      destruct HSL as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8' & S9 & S10 & S11).
      unfold nslots, nslot in *.
      split; [apply SLK; [unfold NS_F0; clear; lia | exact S1]|].
      split; [apply SLK; [unfold NS_FK; clear; lia | exact S2]|].
      split; [apply SLK; [unfold NS_TS; clear; lia | exact S3']|].
      split; [apply SLK; [unfold NS_SB; clear; lia | exact S4]|].
      split; [apply SLK; [unfold NS_PS8; clear; lia | exact S5]|].
      split; [apply SLK; [unfold NS_PS12; clear; lia | exact S6]|].
      split; [apply SLK; [unfold NS_SH8; clear; lia | exact S7]|].
      split; [apply SLK; [unfold NS_SH12; clear; lia | exact S8']|].
      split; [apply SLK; [unfold NS_OFF8; clear; lia | exact S9]|].
      split; [apply SLK; [unfold NS_OFF12; clear; lia | exact S10]|].
      apply SLK; [unfold NS_MASK; clear; lia | exact S11].
    + (* the journal's bookkeeping *)
      destruct HJBK as (Hk2 & Hab & Hmo & Hfd0 & Hfs0).
      split; [exact Hk2|]. split; [exact Hab|]. split; [exact Hmo|].
      split; [rewrite Hfd; exact Hfd0 | rewrite Hfs; exact Hfs0].
    + (* the caller's memory and the result *)
      unfold nx_fin_at, nx_fin. right.
      destruct (HSTR Hh) as (Hinh & Hinb & _ & _ & _ & _ & _ & _ & _ & _ & _).
      destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hinh)
        as (_ & Hh4096 & Hhceil & _).
      destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hinb)
        as (_ & Hb4096 & Hbceil & _).
      change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
      pose proof (req_size_pos (Z.of_nat (length (n_C cx))) (Zle_0_nat _)) as [_ Hreqb].
      split; [exact Hh|].
      split; [rewrite R22, (nx_res_fit _ _ _ _ Hfit); reflexivity|].
      split.
      { change (nx_wrset (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx)) with (nx_E cx).
        apply (ts_kept_after (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) W3 (ms_mem ms3) (ms_mem ms')
                 (spZ (n_regs cx)) (nx_E cx) (fun a => n_ts cx <> 0 /\ n_ts cx <= a < n_ts cx + 8) HARc HKEPT HUN).
        - intros a [T0 Ha]. unfold nx_E, nx_wrset. right; right; left. split; [exact T0 | exact Ha].
        - intros a Hi [T0 Ha]. destruct (TAP T0 a Ha) as (_ & _ & _ & _ & _ & _ & _ & _ & Hni). exact (Hni Hi).
        - exact HG. }
      split.
      { apply (asource_at_frame KS (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms'))); [|exact HSRC].
        intros a Ha. apply (mbyte_of_aview SEGS).
        assert (Har : 0 <= a < 2 ^ 64).
        { destruct Ha as [Ha | [Ha | Ha]];
            [clear - Ha Hh4096 Hhceil C1; unfold SRC_FILE_BLOCK in *; lia | clear - Ha Hb4096 Hbceil Hreqb C1; lia |].
          pose proof (pa_segs_low a (proj1 (asil_env _ _ _ _ ASIL a Ha))) as Hlo. clear - Hlo C5. lia. }
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
        intros x Hx. rewrite Hlb, Hlbj in Hx. apply HUN; [clear - Hx Hbuf4 Hbuf63; lia|]. intros [T0 Hy].
        destruct (TAP T0 x Hy) as (_ & _ & _ & _ & _ & Hbf & _). exact (Hbf Hx). }
      intros T0. rewrite (nx_tsv_fit _ _ _ _ _ Hfit). exact (HV T0).
Qed.

(* The phase in the shape the top takes it (PcapSourceNext.v H_fitB). *)
Corollary pb_nx_tsX :
  nx_from SK B KS (nx_post SK B MT KS) (nx_exit_inv B MT KS) -> nx_from SK B KS (nx_post SK B MT KS) (nx_ts_inv B MT KS).
Proof. exact (pb_nx_ts (nx_post SK B MT KS)). Qed.

End c.
End b.
End a.
