(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1w.v (origin/ossv/recipes c8557374ad2e), with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's ASan build. lib_site_x (donor AD1w.v:80-105) RESTATED over pcap's program contract (lib/A/Prog/PcapEntry.v tfib_lib_post_x, porter a Theorem Labs lane rulings 1-3): the callee's journal is W_journal.v's ajournal_gx at the harness globals G_HARNESS (PcapEntry.v:36) with no out window (XO = 0, OUT = []), in place of cgif's YCbq.ajournal, and the callee's output is PWalk.OUT pl (PcapEntry.v:73) in place of cgif's []; FINV is lib/A/AD1u.v's, over pcap's source pcap_KS. The sink head is the Section's SK (no global instance; PcapSinkHeads.v). The fd-names conjunct (Namei.fd_names_path ... YI16.sink_path = false, donor AD1w.v:89, :101, :203) is carried as the donor carries it: sink_path is cgif's literal, inert (no open of it); HOOK: a Theorem Labs lane's image-generic inertness lemma (a working branch lib/Reusable, cited by path once it lands) discharges it. rule 24: no function proved anew. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/AD1w.v, with its module paths and module names changed; 201 of its 228 lines of code are new or changed and 236 lines of the source are left out. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m YA0e.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AsanNoAR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AE2p AE3i AE3h AE3m AE23.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1u AD1w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile LinkExitFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs LinkRwRewind.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The driver's exit with link's memory FILE on musl's open-file list (AD1w.v exit_file_tfa).

   The walk from A_EXIT 0x90688 (jal exit) runs exit 0x90d88, __funcs_on_exit, __libc_exit_fini and the
   memory-checking runtime's module destructor 0x8864c, then __stdio_exit 0x96878 up to +0x14 (0x9688c),
   where ofl_head has just been read into s0. On link that head is the memory FILE f (AD1u.v FINV's amf_gi),
   so the loop body of __stdio_exit visits it; the released walks (AE23.v) read 0 there and fall through.
   The walk is split at the two ends of that loop body:
     exf_head_tfa : A_EXIT .. 0x9688c with s0 = f                (before the loop)
     the loop      : 0x9688c .. 0x96890 with s0 = 0              (exf_loop_empty / exf_loop_pend_tfa)
     exf_tail_tfa : 0x96890 .. the exit ecall                    (after the loop)
   exf_mid is the state both ends of the loop body share. It carries no AR: the module destructor at 0x8864c
   unregisters the runtime's globals (AE37.v x2_rodata) and its contract (AE3h.v xret_realizes_noar) keeps
   none, so every fact the rest of the exit needs is carried here as a fact about the memory. *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section t.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.

(* ex_consts (AE23.v) without the cells that are not constants of this walk: the open-file head, which on
   link holds the memory FILE, and the four that the part of the exit before the loop writes - the three
   atexit cells that __funcs_on_exit clears as it runs a handler, and exit's own lock. The part after the
   loop reads none of them. *)
Definition exf_consts : list (Z * N * Z) :=
  filter (fun c => negb (List.existsb (Z.eqb (fst (fst c)))
                           [0x652308; 0x651c60; 0x651c68; 0x651c70; 0x651e80])) ex_consts.

(* The facts mwrite's flush (lib/A/Rt/LinkRwExitDefs.v amwrite_mf_flush_noar_realizes) needs at 0x9688c that the
   rest of exf_mid does not give, all about the memory because no AR is left after 0x8864c: the memcpy
   interceptor's cells (AE2y.v icpt_rodata), g_said's shadow addressable and readable (the module destructor
   has just set it to 0), and the FILE's block present, off the image, below the stack window, in
   application memory and addressable in the shadow map. *)
Definition exf_noar (W : world tfibsegs) (mem : word -> option byte) (usp f : Z) : Prop :=
acells_ok tfibsegs (mrestrict (w_H W) mem) icpt_rodata /\
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF 0x62fee0 4096 /\
shadow_hull_vis (aview tfibsegs (w_H W) mem) 0x62fee0 4096 /\
(forall a, f <= a < f + AMF_BLOCK -> apresent (w_H W) mem a /\ ~ in_img tfibsegs a) /\
amem_range f AMF_BLOCK /\ f + AMF_BLOCK <= usp - 65536 /\
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF f AMF_BLOCK /\
shadow_hull_vis (aview tfibsegs (w_H W) mem) f AMF_BLOCK.

(* the interceptor's cells lie in [0xa19c8, 0xab138), apart from the two cells of that range that the module
   destructor writes (AE23.v XW2), so a memory that agrees there keeps them *)
Definition icpt_cell_ok (a n : Z) : bool :=
  (0xa19c8 <=? a) && (a + n <=? 0xab138) && ((a + n <=? 0xa6d80) || (0xa6d88 <=? a)) &&
  ((a + n <=? 0xa7cf0) || (0xa7cf8 <=? a)).
Lemma icpt_cells_chk : forallb (fun r => forallb (fun c =>
  icpt_cell_ok (fst (fst r) + fst (fst c)) (Z.of_N (snd (fst c)))) (snd r)) icpt_rodata = true.
Proof. vm_compute. reflexivity. Qed.
Lemma icpt_cells_kept : forall (H H' : word -> bool) (m m' : word -> option byte),
(forall a, 0xa19c8 <= a < 0xab138 -> ~ (0xa6d80 <= a < 0xa6d88) -> ~ (0xa7cf0 <= a < 0xa7cf8) ->
   aview tfibsegs H' m' a = aview tfibsegs H m a) ->
acells_ok tfibsegs (mrestrict H m) icpt_rodata -> acells_ok tfibsegs (mrestrict H' m') icpt_rodata.
Proof.
intros H H' m m' Hfr HC. unfold acells_ok in *. rewrite Forall_forall in HC |- *.
intros r Hr. specialize (HC r Hr). rewrite Forall_forall in HC |- *. intros c Hc. specialize (HC c Hc).
pose proof (proj1 (forallb_forall _ _) icpt_cells_chk r Hr) as Cr. cbv beta in Cr.
pose proof (proj1 (forallb_forall _ _) Cr c Hc) as Cc. unfold icpt_cell_ok in Cc.
apply andb_prop in Cc as [Cc C4]. apply andb_prop in Cc as [Cc C3]. apply andb_prop in Cc as [C1 C2].
apply Z.leb_le in C1. apply Z.leb_le in C2.
apply (val_mem_kept H H' m m'); [|exact HC].
intros kk Hk. rewrite N_nat_Z in Hk. apply Hfr; [lia | |].
- apply orb_prop in C3 as [C3|C3]; apply Z.leb_le in C3; lia.
- apply orb_prop in C4 as [C4|C4]; apply Z.leb_le in C4; lia.
Qed.

(* a memory that agrees on the shadow hull of [x, x + n) keeps that hull readable *)
Lemma hull_kept : forall (rd rd' : Z -> option Z) x n,
(forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof. intros rd rd' x n Heq H s Hs. rewrite (Heq s Hs). exact (H s Hs). Qed.

(* The state at both ends of the loop body, at 0x9688c and at 0x96890. The stack cells are exit's and
   __stdio_exit's saved registers: exit's frame is [usp - 64, usp - 48), __stdio_exit's [usp - 80, usp - 64),
   so the exit code, which exit holds in s0, is saved at usp - 80 while s0 holds the open-file list. *)
Definition exf_mid (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (usp code f : Z) (k : nat) (fs : Fs) (tid cval sew : Z) : Prop :=
spZ regs = usp - 80 /\ usp mod 16 = 0 /\ sp_window_lo <= usp <= sp_window_hi /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ as_tp B = TFIB_TPX /\
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 80) 8 code /\ (code = 0 \/ code = 2) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 72) 8 0x90df4 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (usp - 56) 8 0x9068c /\
cells_are exf_consts (mrestrict (w_H W) mem) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid /\ 0 < tid < 2 ^ 31 /\
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary /\
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval /\ 0 <= cval < 2 ^ 64 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew /\
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew /\ 0 <= sew < 2 ^ 64 /\
((k = 0%nat /\ stdout_img (w_H W) mem) \/ ((1 <= k)%nat /\ xst k (w_H W) mem)) /\
(forall fd, fd_lookup (m_fds md) fd = fd_lookup APSG.fds_std fd) /\ m_fs md = fs /\
amf_gi tfibsegs link_amf [(f, AMF_BLOCK)] (mrestrict (w_H W) mem) /\
4096 <= f /\ f mod 16 = 0 /\ f + AMF_BLOCK <= 2 ^ 47 /\ exf_noar W mem usp f.

(* 1. the head: from the state exit_file_tfa gives at A_EXIT to 0x9688c, with s0 = the FILE
      (proved in LinkDrvExitFH2.v, exf_head_ok; at PcapB and AD1k.xst exf_head_link) *)
Definition exf_head_tfa : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (fs : Fs) (code : Z) (k : nat) (f : Z),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 code -> (code = 0 \/ code = 2) -> spZ regs = usp - 48 ->
getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_L ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
((k = 0%nat /\ stdout_img (w_H W) mem) \/ ((1 <= k)%nat /\ xst k (w_H W) mem)) ->
(forall j, fd_lookup (m_fds md) j = fd_lookup APSG.fds_std j) -> m_fs md = fs ->
FINV [(f, AMF_BLOCK)] (w_H W) mem -> In (f, AMF_BLOCK) (ablocks B ly S) ->
SRr tfibsegs W (cfg_at tfibsegs A_EXIT regs mem md)
 (fun W' c' => W' = W /\ exists regs1 mem1 md1 tid cval sew,
    c' = cfg_at tfibsegs A_SX_LOOP regs1 mem1 md1 /\ getr regs1 8%bv = w64 f /\
    exf_mid W regs1 mem1 md1 usp code f k fs tid cval sew).

(* 2. the loop body when the FILE's window holds bytes: f->write (f, 0, 0) is mwrite's flush.
      amwrite_mf_flush_noar_realizes (lib/A/Rt/LinkRwExitDefs.v) is the
      contract of that call at this state (proved in LinkDrvExitFP.v, exf_loop_pend_ok; at AD1k.xst
      exf_loop_pend_link). *)
Definition exf_loop_pend_tfa : Prop :=
forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(usp code f : Z) (k : nat) (fs : Fs) (tid cval sew wpos wbase : Z),
exf_mid W regs mem md usp code f k fs tid cval sew -> getr regs 8%bv = w64 f ->
val_mem tfibsegs (mrestrict (w_H W) mem) (f + 40) 8 wpos ->
val_mem tfibsegs (mrestrict (w_H W) mem) (f + 56) 8 wbase -> wpos <> wbase ->
SRr tfibsegs W (cfg_at tfibsegs A_SX_LOOP regs mem md)
 (fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at tfibsegs A_SX_NEXT regs' mem' md' /\ getr regs' 8%bv = w64 0 /\
    exf_mid W regs' mem' md' usp code f k fs tid cval sew).

(* 3. the tail: the rest of __stdio_exit (stdin, stdout, stderr) and _Exit *)
Definition exf_tail_tfa : Prop :=
forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(usp code f : Z) (k : nat) (fs : Fs) (tid cval sew : Z),
AI tfibsegs (w_H W) (w_A W) md ->
exf_mid W regs mem md usp code f k fs tid cval sew -> getr regs 8%bv = w64 0 ->
srealizes tfibsegs (cfg_at tfibsegs A_SX_NEXT regs mem md)
  (wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).

Hypothesis EXFH : exf_head_tfa.
Hypothesis EXFP : exf_loop_pend_tfa.
Hypothesis EXFT : exf_tail_tfa.

(* the model keeps the file descriptors and the file system over a materialization *)
Lemma sbm_fds_fs : forall md md', same_but_materialized md md' ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros md md' H. rewrite (same_but_materialized_wvb md md' H). split; destruct md; reflexivity.
Qed.

(* the FILE's fixed words the loop body reads, from the GI conjunct *)
Lemma exf_file_fixed : forall (W : world tfibsegs) (mem : word -> option byte) f,
amf_gi tfibsegs link_amf [(f, AMF_BLOCK)] (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (f + 72) 8 LA_MWRITE /\
val_mem tfibsegs (mrestrict (w_H W) mem) (f + 140) 4 AU32M1 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (f + 8) 8 0 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (f + 16) 8 0 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (f + 112) 8 0.
Proof.
intros W mem f Hgi.
destruct Hgi as [(_ & Hnil) | (f' & _ & Hl & Hat)]; [discriminate Hnil|].
injection Hl as Hff. subst f'.
pose proof (amemfile_close_reads tfibsegs link_amf _ f Hat) as (V140 & V72 & V8 & V16 & V112).
split; [exact V72|]. split; [exact V140|]. split; [exact V8|]. split; [exact V16 | exact V112].
Qed.

(* the FILE's write window, from the GI conjunct *)
Lemma exf_file_win : forall (W : world tfibsegs) (mem : word -> option byte) f,
amf_gi tfibsegs link_amf [(f, AMF_BLOCK)] (mrestrict (w_H W) mem) -> f + AMF_BLOCK <= 2 ^ 47 ->
exists wpos wbase, val_mem tfibsegs (mrestrict (w_H W) mem) (f + 40) 8 wpos /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 56) 8 wbase /\
  0 <= wpos < 2 ^ 64 /\ 0 <= wbase < 2 ^ 64.
Proof.
intros W mem f Hgi Hf47.
destruct Hgi as [(_ & Hnil) | (f' & _ & Hl & Hat)]; [discriminate Hnil|].
injection Hl as Hff. subst f'.
pose proof Hat as (Hf0 & Hfh & _ & _ & _ & _ & Hwin & _).
destruct Hwin as (_ & _ & Hw).
assert (KS : AMF_BLOCK = 1304 /\ AMF_BUF = 280 /\ AMF_BUFSIZ = 1024) by (repeat split; reflexivity).
destruct KS as (KB & KBF & KBS).
assert (R47 : 2 ^ 47 < 2 ^ 64) by (vm_compute; reflexivity).
destruct Hw as [(W32 & W40 & W56) | (kk & Hkk & W32 & W40 & W56)].
- exists 0, 0. split; [exact W40|]. split; [exact W56|]. split; lia.
- exists (f + AMF_BUF + kk), (f + AMF_BUF).
  split; [exact W40|]. split; [exact W56|]. split; lia.
Qed.

(* the loop body when the FILE's window holds nothing: no call, and the memory is unchanged *)
Lemma exf_loop_empty : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(usp code f : Z) (k : nat) (fs : Fs) (tid cval sew wpos wbase : Z),
exf_mid W regs mem md usp code f k fs tid cval sew -> getr regs 8%bv = w64 f ->
val_mem tfibsegs (mrestrict (w_H W) mem) (f + 40) 8 wpos ->
val_mem tfibsegs (mrestrict (w_H W) mem) (f + 56) 8 wbase -> wpos = wbase ->
0 <= wpos < 2 ^ 64 -> 0 <= wbase < 2 ^ 64 ->
SRr tfibsegs W (cfg_at tfibsegs A_SX_LOOP regs mem md)
 (fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at tfibsegs A_SX_NEXT regs' mem' md' /\ getr regs' 8%bv = w64 0 /\
    exf_mid W regs' mem' md' usp code f k fs tid cval sew).
Proof.
intros W regs mem md usp code f k fs tid cval sew wpos wbase MID G8 V40 V56 Heq Rp Rb.
pose proof MID as (Msp & M16 & Musp & Mgp & Mtp & Mtpx & Mpres & Mcode & Mc02 & Mra & Mra2 &
  Mcells & Mtid & Mtidr & Mgot & Mcan & Mcanr & Msew1 & Msew2 & Msewr & Mso & Mfds & Mfs & Mgi & Mf4 & Mf16 & Mfh &
  Mnoar).
destruct (exf_file_fixed W mem f Mgi) as (V72 & V140 & V8 & V16 & V112).
eapply SRr_bind; [exact (xf_head W regs mem md f wpos wbase G8 Mf4 Mfh Mf16 V40 V56 V72 V140 Rp Rb)|].
cbv beta. intros W1 c1 _ (-> & regs1 & md1 & Hsb1 & HP1 & [(_ & ->) | (Hne & _)]); [|exfalso; exact (Hne Heq)].
assert (G8_1 : getr regs1 8%bv = w64 f)
  by (rewrite (ap_lit regs regs1 8%bv 8 HP1 ltac:(unfold acallee_saved; lia) eq_refl); exact G8).
eapply SRr_bind; [exact (xf_tail W regs1 mem md1 f G8_1 Mf4 Mfh Mf16 V8 V16 V112)|].
cbv beta. intros W2 c2 _ (-> & regs2 & md2 & -> & Hsb2 & R8 & HP2).
apply SRr_ret. split; [reflexivity|]. exists regs2, mem, md2.
split; [reflexivity|]. split; [exact R8|].
assert (KEEP : forall (r : bv 5) (z : Z), acallee_saved z -> z <> 8 -> bv_unsigned r = z ->
  getr regs2 r = getr regs r).
{ intros r z Hz H8 Hr. subst z.
  pose proof (HP2 (bv_unsigned r) Hz H8) as X2. pose proof (HP1 (bv_unsigned r) Hz) as X1.
  rewrite !Z_to_bv_bv_unsigned in X2, X1. rewrite X2. exact X1. }
assert (SB : same_but_materialized md md2)
  by exact (same_but_materialized_trans _ _ _ Hsb1 Hsb2).
unfold exf_mid.
split; [unfold spZ; rewrite (KEEP 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(lia) eq_refl); exact Msp|].
split; [exact M16|]. split; [exact Musp|].
split; [rewrite (KEEP 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(lia) eq_refl); exact Mgp|].
split; [rewrite (KEEP 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(lia) eq_refl); exact Mtp|].
split; [exact Mtpx|]. split; [exact Mpres|]. split; [exact Mcode|]. split; [exact Mc02|].
split; [exact Mra|]. split; [exact Mra2|]. split; [exact Mcells|].
split; [exact Mtid|]. split; [exact Mtidr|]. split; [exact Mgot|]. split; [exact Mcan|].
split; [exact Mcanr|]. split; [exact Msew1|]. split; [exact Msew2|]. split; [exact Msewr|].
split; [exact Mso|].
split; [intros fd; rewrite (proj1 (sbm_fds_fs md md2 SB)); exact (Mfds fd)|].
split; [rewrite (proj2 (sbm_fds_fs md md2 SB)); exact Mfs|].
split; [exact Mgi|]. split; [exact Mf4|]. split; [exact Mf16|]. split; [exact Mfh | exact Mnoar].
Qed.

Theorem tfib_exit_file : exit_file_tfa B xst.
Proof.
intros E' W regs mem md ly S usp fs code k f E0 U U16 Htid Ra0 Hc02 Hsp R3 R4 HM Hwin HAI HAR HTOP Hnev HSO Hfds Hfs HFI Hblk.
change (mkCfg (mkst regs (w64 A_EXIT) mem (seg_rom tfibsegs)) md)
  with (cfg_at tfibsegs A_EXIT regs mem md).
apply (SRr_srealizes tfibsegs W (cfg_at tfibsegs A_EXIT regs mem md) _ _
  (EXFH E' W regs mem md ly S usp fs code k f E0 U U16 Htid Ra0 Hc02 Hsp R3 R4 HM Hwin HAI HAR HTOP Hnev HSO Hfds Hfs HFI Hblk) HAI).
intros W1 c1 _ HAI1 (-> & regs1 & mem1 & md1 & tid & cval & sew & -> & G8 & MID).
pose proof MID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Mgi & _ & _ & Mfh & _).
destruct (exf_file_win W mem1 f Mgi Mfh) as (wpos & wbase & V40 & V56 & Rp & Rb).
destruct (Z.eq_dec wpos wbase) as [Heq | Hne].
- apply (SRr_srealizes tfibsegs W (cfg_at tfibsegs A_SX_LOOP regs1 mem1 md1) _ _
    (exf_loop_empty W regs1 mem1 md1 usp code f k fs tid cval sew wpos wbase MID G8 V40 V56 Heq Rp Rb) HAI1).
  intros W2 c2 _ HAI2 (-> & regs2 & mem2 & md2 & -> & R8 & MID2).
  exact (EXFT W regs2 mem2 md2 usp code f k fs tid cval sew HAI2 MID2 R8).
- apply (SRr_srealizes tfibsegs W (cfg_at tfibsegs A_SX_LOOP regs1 mem1 md1) _ _
    (EXFP W regs1 mem1 md1 usp code f k fs tid cval sew wpos wbase MID G8 V40 V56 Hne) HAI1).
  intros W2 c2 _ HAI2 (-> & regs2 & mem2 & md2 & -> & R8 & MID2).
  exact (EXFT W regs2 mem2 md2 usp code f k fs tid cval sew HAI2 MID2 R8).
Qed.

End t.
End d.
