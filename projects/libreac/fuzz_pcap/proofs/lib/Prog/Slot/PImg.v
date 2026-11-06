From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_next_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac.
Import ListNotations.
Open Scope Z_scope.

(* The facts that connect the image's bytes to the stdio predicates of StdioModel: the stderr FILE at A_STDERR
   (errf), the mode field that GI reads, the RELRO words that point to it, and the stdio state at entry. *)

(* The stderr FILE's cells before its mode field (offset 136) and after it (offset 140). *)
Definition stderr_pre (fl : Z) : list Cells.cell :=
  [ Cells.C4 (wz fl); Cells.C4 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz A_STDIO_CLOSE);
    Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0);
    Cells.C8 (wz 0); Cells.C8 (wz A_STDIO_WRITE); Cells.C8 (wz A_STDIO_SEEK); Cells.C8 (wz A_STDERR_BUF);
    Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0);
    Cells.C4 (wz 2); Cells.C4 (wz 0); Cells.C8 (wz 0) ].
Definition stderr_post : list Cells.cell :=
  [ Cells.C4 (wz 4294967295); Cells.C4 (wz 4294967295); Cells.C4 (wz 0);
    Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0);
    Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0); Cells.C8 (wz 0) ].

Lemma stderr_cells_split : forall fl md, stderr_cells fl md = stderr_pre fl ++ Cells.C4 (wz md) :: stderr_post.
Proof. intros fl md. reflexivity. Qed.

Lemma stderr_bytes_split : forall fl md, Cells.cells_bytes (stderr_cells fl md) =
  Cells.cells_bytes (stderr_pre fl) ++ le4 (wz md) ++ Cells.cells_bytes stderr_post.
Proof. intros fl md. rewrite stderr_cells_split, Cells.cells_bytes_app. reflexivity. Qed.

Lemma stderr_pre_len : forall fl, length (Cells.cells_bytes (stderr_pre fl)) = 136%nat.
Proof. intros fl. reflexivity. Qed.

Lemma stderr_post_len : length (Cells.cells_bytes stderr_post) = 92%nat.
Proof. reflexivity. Qed.

Lemma stderr_len : forall fl md, length (Cells.cells_bytes (stderr_cells fl md)) = 232%nat.
Proof. intros fl md. reflexivity. Qed.

Lemma stderr_wf : forall fl md, Cells.cells_wf (stderr_cells fl md).
Proof. intros fl md. unfold stderr_cells. cbn. tauto. Qed.

(* Every memory may store to the stderr FILE (img_w_wr). *)
Lemma stderr_wr : forall m fl md, wr_at rsegs m A_STDERR (Z.of_nat (Cells.cells_size (stderr_cells fl md))).
Proof.
  intros m fl md. change (Z.of_nat (Cells.cells_size (stderr_cells fl md))) with 232.
  split; [unfold A_STDERR; lia|]. split; [unfold A_STDERR; lia|]. intros i Hi.
  exact (proj1 (img_w_wr m (A_STDERR + i) ltac:(right; right; lia))).
Qed.

(* Membership in frame_RELRO, decided on the list. *)
Definition rel_in (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) frame_RELRO.

Lemma rel_in_ok : forall a, rel_in a = true -> in_globals frame_RELRO a.
Proof.
  intros a H. unfold rel_in in H. apply existsb_exists in H as ([lo len] & Hin & H).
  cbn [fst snd] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists lo, len. split; [exact Hin | lia].
Qed.

Definition rel_rng (a : Z) (n : nat) : bool := forallb (fun i => rel_in (a + Z.of_nat i)) (seq 0 n).

Lemma rel_rng_ok : forall a n, rel_rng a n = true -> forall i, (i < n)%nat -> in_globals frame_RELRO (a + Z.of_nat i).
Proof.
  intros a n H i Hi. apply rel_in_ok. unfold rel_rng in H. rewrite forallb_forall in H. apply H.
  apply in_seq. lia.
Qed.

(* The image holds bs at a, and a .. a + |bs| lies in frame_RELRO. *)
Definition rel_img (a : Z) (bs : list byte) : bool :=
  ss_rel_chk a bs && rel_rng a (length bs) && (0 <=? a) && (a + Z.of_nat (length bs) <=? 2 ^ 64).

(* The image's stderr FILE outside its mode field is that of stderr_cells 5. *)
Lemma stderr_img_chk :
  (rel_img A_STDERR (Cells.cells_bytes (stderr_pre 5)) && rel_img (A_STDERR + 140) (Cells.cells_bytes stderr_post))%bool
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma got_img_chk :
  (rel_img A_GOT_STDERR (le8 (wz A_STDERR_VAR)) && rel_img A_STDERR_VAR (le8 (wz A_STDERR)))%bool = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bytes_img_at : forall m a bs i, bytes_at rsegs m a bs -> rel_img a bs = true -> (i < length bs)%nat ->
  mbyte rsegs m (a + Z.of_nat i) = seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)).
Proof.
  intros m a bs i (_ & _ & H) C Hi. unfold rel_img in C.
  apply andb_prop in C as [C _]. apply andb_prop in C as [C _]. apply andb_prop in C as [C _].
  rewrite (ss_rel_chk_ok bs a C i Hi). exact (H i Hi).
Qed.

Lemma rel_not_mode : forall a, in_globals frame_RELRO a -> ~ (A_STDERR + 136 <= a < A_STDERR + 140).
Proof.
  intros a (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn [In] in Hin. unfold A_STDERR.
  repeat (destruct Hin as [E|Hin]; [injection E as E1 E2; subst; lia|]). destruct Hin.
Qed.

(* The three parts of an errf FILE: before the mode field, the mode field (GI's bytes), after it. *)
Lemma errf_parts : forall m fl md, errf m fl md ->
  bytes_at rsegs m A_STDERR (Cells.cells_bytes (stderr_pre fl)) /\
  bytes_at rsegs m (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) (le4 (wz md)) /\
  bytes_at rsegs m (A_STDERR + 140) (Cells.cells_bytes stderr_post).
Proof.
  intros m fl md (((_ & HB) & _) & _ & _). rewrite stderr_bytes_split in HB.
  apply Mem.bytes_at_app in HB as [H1 HB]. rewrite stderr_pre_len in HB.
  apply Mem.bytes_at_app in HB as [H2 H3]. rewrite length_le4 in H3.
  replace (A_STDERR + Z.of_nat 136) with (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) in H2 by (unfold A_STDERR; lia).
  replace (A_STDERR + Z.of_nat 136 + Z.of_nat 4) with (A_STDERR + 140) in H3 by lia.
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* 2. *)
Lemma GI_of_errf : forall j m fl md, errf m fl md -> GI j m.
Proof.
  intros j m fl md HE. destruct (errf_parts m fl md HE) as (_ & H2 & _).
  destruct HE as (_ & _ & [-> | ->]); [left | right]; exact H2.
Qed.

(* bs at a, from the mode-field bytes and the val_mem form of sink_none. *)
Lemma vm_bytes : forall mem a n v bs, val_mem rsegs mem a n v -> length bs = n ->
  (forall k, (k < n)%nat -> nth_error bs k = Some (Z_to_bv 8 (le_byte v n k))) ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> bytes_at rsegs mem a bs.
Proof.
  intros mem a n v bs H Hl Hn Ha Hb. split; [exact Ha|]. split; [rewrite Hl; exact Hb|].
  intros i Hi. rewrite Hl in Hi. rewrite (Hn i Hi). exact (H i Hi).
Qed.

Section I.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

Lemma pi_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma relro_bytes : forall m a bs, relro B m -> rel_img a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs HR H. pose proof H as C. unfold rel_img in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H3. apply Z.leb_le in H4.
  split; [exact H3|]. split; [exact H4|]. intros i Hi.
  pose proof (HR (a + Z.of_nat i) (rel_rng_ok a _ H2 i Hi)) as E. rewrite pi_segs in E.
  change (mbyte rsegs m (a + Z.of_nat i) = nth_error bs i). rewrite E. exact (ss_rel_chk_ok bs a H1 i Hi).
Qed.

Lemma errf_bytes : forall m md, relro B m -> bytes_at rsegs m (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) (le4 (wz md)) ->
  bytes_at rsegs m A_STDERR (Cells.cells_bytes (stderr_cells 5 md)).
Proof.
  intros m md HR HM. pose proof stderr_img_chk as C. apply andb_prop in C as [C1 C2].
  rewrite stderr_bytes_split. apply Mem.bytes_at_app. split; [exact (relro_bytes m _ _ HR C1)|].
  rewrite stderr_pre_len. apply Mem.bytes_at_app. split.
  - replace (A_STDERR + Z.of_nat 136) with (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) by (unfold A_STDERR; lia). exact HM.
  - rewrite length_le4. replace (A_STDERR + Z.of_nat 136 + Z.of_nat 4) with (A_STDERR + 140) by lia.
    exact (relro_bytes m _ _ HR C2).
Qed.

(* 1. *)
Lemma errf_of_img : forall j m, relro B m -> GI j m ->
  exists md, (md = 0 \/ md = 4294967295) /\ errf m 5 md.
Proof.
  intros j m HR [HG|HG]; [exists 0 | exists 4294967295]; (split; [lia|]);
    (split; [|split; [left; reflexivity | lia]]);
    (split; [split; [apply stderr_wf | exact (errf_bytes m _ HR HG)] | apply stderr_wr]).
Qed.

(* 3. *)
Lemma relro_of_errf : forall m m' md', relro B m -> errf m' 5 md' ->
  (forall a, in_globals frame_RELRO a -> ~ (A_STDERR <= a < A_STDERR + 232) ->
     mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a) ->
  relro B m'.
Proof.
  intros m m' md' HR HE HK a Ha.
  destruct (Z_lt_le_dec a A_STDERR) as [Hlo|Hlo].
  { rewrite (HK a Ha ltac:(lia)). exact (HR a Ha). }
  destruct (Z_lt_le_dec a (A_STDERR + 232)) as [Hhi|Hhi].
  2: { rewrite (HK a Ha ltac:(lia)). exact (HR a Ha). }
  pose proof (rel_not_mode a Ha) as Hm. destruct (errf_parts m' 5 md' HE) as (H1 & _ & H3).
  pose proof stderr_img_chk as C. apply andb_prop in C as [C1 C2].
  rewrite pi_segs.
  destruct (Z_lt_le_dec a (A_STDERR + 136)) as [Hp|Hp].
  - replace a with (A_STDERR + Z.of_nat (Z.to_nat (a - A_STDERR))) by lia.
    apply (bytes_img_at m' A_STDERR (Cells.cells_bytes (stderr_pre 5))); [exact H1 | exact C1 |].
    rewrite stderr_pre_len. lia.
  - replace a with (A_STDERR + 140 + Z.of_nat (Z.to_nat (a - (A_STDERR + 140)))) by lia.
    apply (bytes_img_at m' (A_STDERR + 140) (Cells.cells_bytes stderr_post)); [exact H3 | exact C2 |].
    rewrite stderr_post_len. lia.
Qed.

(* 4. *)
Lemma got_of_relro : forall m, relro B m ->
  bytes_at rsegs m A_GOT_STDERR (le8 (wz A_STDERR_VAR)) /\ bytes_at rsegs m A_STDERR_VAR (le8 (wz A_STDERR)).
Proof.
  intros m HR. pose proof got_img_chk as C. apply andb_prop in C as [C1 C2].
  split; [exact (relro_bytes m _ _ HR C1) | exact (relro_bytes m _ _ HR C2)].
Qed.

(* 6. *)
Lemma errf_keep : forall m m' fl md, errf m fl md ->
  (forall i, 0 <= i < 232 -> mbyte (ms_segs B) m' (A_STDERR + i) = mbyte (ms_segs B) m (A_STDERR + i)) ->
  errf m' fl md.
Proof.
  intros m m' fl md (((Hwf & HB) & _) & Hfl & Hmd) HK.
  split; [|split; [exact Hfl | exact Hmd]].
  split; [split; [exact Hwf|] | apply stderr_wr].
  apply (ss_bytes_mbyte rsegs m m'); [|exact HB]. intros i Hi.
  rewrite stderr_len in Hi. rewrite <- pi_segs. apply HK. lia.
Qed.

(* 5: the stdio state of every allocator state with no sink open: sink_none gives __libc+1, the open-file lock
   and the open-file head; ax_statics (AllocExtra of frame_allocator) gives __libc+3 and the guard words. *)
Lemma stdio_of_MR : forall L A mem md, aa_MR (APIf rc) L A mem md -> sink_none B mem md ->
  stdio_ok mem /\ ofl_empty mem /\ guard_ok mem.
Proof.
  intros L A mem md HM ((HT & HL) & HH & _).
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  destruct (ALLOC rc fx0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AX & _).
  destruct (ax_statics AX L A mem md HM) as (Gw & (g & Hg & Gg) & L3).
  rewrite GOT, GUA, SEG in Gw. rewrite GUA, SEG in Gg. rewrite LIBC, SEG in L3.
  rewrite THR, SEG in HT. rewrite OFL, SEG in HL. rewrite OFH, SEG in HH.
  split; [split; [|split]|split].
  - unfold A_LIBC. apply (vm_bytes mem _ 1 0); [exact HT | reflexivity | | lia | lia].
    intros k Hk. destruct k as [|k]; [reflexivity | lia].
  - split; [unfold A_LIBC; lia|]. split; [cbn [length]; unfold A_LIBC; lia|].
    intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
    change (mbyte rsegs mem (A_LIBC + 3 + Z.of_nat 0) = nth_error [Z_to_bv 8 0] 0).
    unfold A_LIBC. replace ((symaddr Symbols.Plain.s___libc) + 3 + Z.of_nat 0) with ((symaddr Symbols.Plain.s___libc) + 3) by lia. exact L3.
  - unfold A_OFL_LOCK. apply (vm_bytes mem _ 4 0); [exact HL | apply length_le4 | | lia | lia].
    intros k Hk. do 4 (destruct k as [|k]; [reflexivity|]). lia.
  - split; [split; [cbn; tauto|] |].
    + cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r. unfold A_OFL_HEAD.
      apply (KindBGlue.word_mem_le8 rsegs); [exact HH | lia | lia | lia].
    + change (Z.of_nat (Cells.cells_size [Cells.C8 (wz 0)])) with 8.
      split; [unfold A_OFL_HEAD; lia|]. split; [unfold A_OFL_HEAD; lia|]. intros i Hi.
      exact (proj1 (img_w_wr mem (A_OFL_HEAD + i) ltac:(right; left; lia))).
  - unfold guard_ok. split.
    + unfold A_GOT_GUARD, A_GUARD, wz. apply (KindBGlue.word_mem_le8 rsegs); [exact Gw | lia | lia | lia].
    + exists (Z_to_bv 64 g). unfold A_GUARD. apply (KindBGlue.word_mem_le8 rsegs); [exact Gg | lia | lia | lia].
Qed.

(* 5. *)
Lemma stdio_of_entry : forall g, GV B empty g ->
  lib_pre B (APIf rc) SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) ->
  stdio_ok (g_mem g) /\ ofl_empty (g_mem g) /\ guard_ok (g_mem g).
Proof.
  intros g HGV (HM & _). pose proof HGV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & _).
  exact (stdio_of_MR _ _ _ _ HM HS).
Qed.

Lemma stdio_of_inv : forall g c, Inv_ENTRY B APIf ra empty g c ->
  stdio_ok (g_mem g) /\ ofl_empty (g_mem g) /\ guard_ok (g_mem g).
Proof.
  intros g c (fx' & _ & _ & HGV & HP & _). exact (stdio_of_entry g HGV HP).
Qed.

End I.
