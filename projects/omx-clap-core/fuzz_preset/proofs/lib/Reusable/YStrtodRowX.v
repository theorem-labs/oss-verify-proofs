(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the musl strtod CALL-SITE ROW over YCbqG.v's ajournal_x, GENERIC over the allocator
   invariant ARx (Section Variables segs B ARx) and over the image (strtod_img: the constants of one image's
   lib/{A,B}/Prog/strtod_c.v). No image numeral, no lib/A or lib/B import.
   1. strtod_contract_g: lib/{A,B}/Prog/strtod_x.v strtod_contract_x (h-verbs-1, cold/h-verbs-1-preset-strtodB) with
      the entry address pc, the image constants and the model sm as parameters; the instance files prove it by
      `exact strtod_x_holds`.
   2. astrtod_realizes_x: the call-site text in FCiface.v's ecall_pre_x form, the one text agreed for the stand-ins of
      h-rw-pre-7 (lib/B/Prog/ExvB_Stmt.v:89, origin/cold/h-rw-pre-7-b-ex_value), h-w6u-pre (lib/A/Prog/S8aNumCut.v:67,
      origin/cold/h-hpreset-7-walk-S8a-number) and h-verbs-3 (lib/A/VrdNum.v H_strtod, origin/cold/h-verbs-3-vnum):
      ExvB's text, its end cell stated by properties, with S8a's s + len + 1 <= 2 ^ 62 and presence growth, and the
      facts strtod_x_holds needs that no stand-in states (the caller's stack bounds of YCbq.v astk_ok and
      strtod_site_x). astrtod_realizes_x_of proves it from the callee in strtod_x_holds's form.
   3. aj_strtod_at_x: the row over ajournal_x in YGcallMx.v aj_strlen_at_x's shape (the caller's journal kept at the
      call's state, k unchanged), whose end cell is a byte the caller's journal lets it write (awr_byte) or a footprint
      byte of one of its entry frames (YCbqG.v wr_fp_frame); ajournal_x_after_write_x is YCbqG.v
      ajournal_x_after_write with those and the errno cell in the write set.
   aj_memnorm (lib.Lib.Mem.mem_inv /\ MemNorm.task_mem) is a HYPOTHESIS, not an AR_laws_x field: no ARx instance can
   discharge it today (h-mani-a8, ARcf owner, 2026-10-29: no cf file states it). Two pieces are missing, and the WORLD
   layer owns them, not the allocator instance: (1) a start-up fact, that the loader state satisfies aj_memnorm; (2) a
   step lemma, that each store through wview into a writable segment preserves it. With both, an instance proves it
   and the three walks that carry it (ExValueB eh_memnorm, PValueB, h-w6u-pre's S8a) drop the hypothesis.
   Both posts give aj_memnorm back, so a caller keeps it across strtod: astrtod_realizes_x's last conjunct
   (aj_memnorm mem -> aj_memnorm mem') and aj_strtod_row's last conjunct aj_memnorm mem2. The keep is proved from the
   run: strtod_contract_g's post states mem_inv /\ task_mem at the end memory, and strtod_x_holds proves it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG FCiface YK0o YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0d YGcallMx YA0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Cells Step Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Record strtod_img : Type := MkStrtodImg {
  si_k : Z; si_tp : Z; si_errno : Z; si_got_guard : Z; si_guard : Z; si_globals_top : Z; si_img_lo : Z }.

Section c. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Variable I : strtod_img.
Definition strtod_scratch_g (regs : bvmap 5 word) (e a : Z) : Prop :=
  (YO0d.spZ regs - si_k I <= a < YO0d.spZ regs) \/ (e <= a < e + 8) \/ (si_errno I <= a < si_errno I + 4).
Definition strtod_vis_g (regs : bvmap 5 word) (s e : Z) (txt : list Z) (a : Z) : Prop :=
  (s <= a < s + Z.of_nat (length txt) + 1) \/ strtod_scratch_g regs e a \/
  (si_got_guard I <= a < si_got_guard I + 8) \/ (si_guard I <= a < si_guard I + 8).
Variable sm : list Z -> option (Z * Z).
Variable ainv : (word -> option byte) -> Model -> Prop.
Variable aown : Z -> Prop.
Definition strtod_frame_g : Prop := forall mem md mem' md',
  ainv mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> aown a -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, mbyte segs mem a <> None -> mbyte segs mem' a <> None) ->
  (forall a, YO0d.present mem a -> YO0d.present mem' a) ->
  same_but_materialized md md' ->
  ainv mem' md'.
Definition strtod_post_g (regs : bvmap 5 word) (s e : Z) (txt : list Z) (mem : word -> option byte) (md : Model)
    (fx' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  exists (bits c : Z) (ev' : word),
    ainv mem' md' /\ same_but_materialized md md' /\
    sm txt = Some (bits, c) /\ 0 <= c <= Z.of_nat (length txt) /\
    reg_get (@fp_regs fx') 10 = Z_to_bv 64 bits /\
    (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 ->
       reg_get (@fp_regs fx') k = reg_get (@fp_regs fx) k) /\
    YO0d.regs_preserved regs regs' /\ getr regs' 1 = getr regs 1 /\
    lib.Lib.Step.rw_cells segs mem' e [lib.Lib.Cells.C8 (Z_to_bv 64 (s + c))] /\
    lib.Lib.Step.rw_cells segs mem' (si_errno I) [lib.Lib.Cells.C4 ev'] /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ strtod_scratch_g regs e a ->
       mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
    (forall a, YO0d.present mem a -> YO0d.present mem' a) /\
    (forall a, writable_at segs mem a -> writable_at segs mem' a) /\
    lib.Lib.Mem.mem_inv segs mem' /\ MemNorm.task_mem segs mem' /\
    lib.Lib.Frame.stk segs mem' (YO0d.spZ regs - si_k I) (YO0d.spZ regs).
Definition strtod_contract_g (pc : Z) : Prop :=
  forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
         (s e : Z) (txt : list Z) (ejunk canary ev : word),
    getr regs 10 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 e -> getr regs 4 = Z_to_bv 64 (si_tp I) ->
    lib.Lib.Mem.bytes_at segs mem s (map (Z_to_bv 8) (txt ++ [0])) ->
    Forall (fun c => FmtFp_facts3.is_numch c = true) txt -> Z.of_nat (length txt) < 2^30 ->
    lib.Lib.Step.rw_cells segs mem e [lib.Lib.Cells.C8 ejunk] ->
    lib.Lib.Frame.stk segs mem (YO0d.spZ regs - si_k I) (YO0d.spZ regs) ->
    si_globals_top I <= YO0d.spZ regs - si_k I -> YO0d.spZ regs < 2^62 ->
    4096 <= s -> s + Z.of_nat (length txt) + 1 <= 2^62 ->
    ((s + Z.of_nat (length txt) + 1 <= si_img_lo I \/ si_globals_top I <= s)
       /\ s + Z.of_nat (length txt) + 1 <= YO0d.spZ regs - si_k I
     \/ YO0d.spZ regs <= s) ->
    (si_globals_top I <= e /\ e + 8 <= YO0d.spZ regs - si_k I \/ YO0d.spZ regs <= e) -> e + 8 <= 2^62 ->
    (e + 8 <= s \/ s + Z.of_nat (length txt) + 1 <= e) ->
    lib.Lib.Step.rw_cells segs mem (si_got_guard I) [lib.Lib.Cells.C8 (Z_to_bv 64 (si_guard I))] ->
    lib.Lib.Step.rw_cells segs mem (si_guard I) [lib.Lib.Cells.C8 canary] ->
    lib.Lib.Step.rw_cells segs mem (si_errno I) [lib.Lib.Cells.C4 ev] ->
    lib.Lib.Mem.mem_inv segs mem -> MemNorm.task_mem segs mem -> frm_zero (@fp_csr fx) ->
    (forall a, strtod_vis_g regs s e txt a -> w_H W (Z_to_bv 64 a) = false) ->
    ainv mem md -> (forall a, strtod_scratch_g regs e a -> ~ aown a) ->
    SRr segs W (mkCfg (@mkst fx regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun W' c' => W' = W /\
         exists (fx' : FPState) regs' mem' md',
           c' = mkCfg (@mkst fx' regs' (v_jalr (getr regs 1) 0) mem' (seg_rom segs)) md' /\
           frm_zero (@fp_csr fx') /\
           strtod_post_g regs s e txt mem md fx' regs' mem' md').
End c.

Section h.
Variable segs : list Segment.

Lemma srx_shiftr_nth : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
- rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma srx_bv8_mod : forall x, Z_to_bv 8 x = Z_to_bv 8 (x mod 256).
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma srx_le8_nth : forall v k, (k < 8)%nat ->
  nth_error (lib.Lib.Mem.le8 (Z_to_bv 64 v)) k = Some (Z_to_bv 8 (le_byte v 8 k)).
Proof.
intros v k Hk. rewrite <- lib.Lib.Step.store_bytes_8'. rewrite srx_shiftr_nth by exact Hk.
rewrite Z_to_bv_unsigned. unfold le_byte, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (8 * Z.of_nat 8) with 64. rewrite <- srx_bv8_mod. reflexivity.
Qed.

Lemma srx_le8_back : forall bs : list byte, length bs = 8%nat -> lib.Lib.Mem.le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. rewrite <- lib.Lib.Step.store_bytes_8'. unfold le_bytes_to_word.
pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as HB. rewrite HL in HB.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HB.
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
rewrite <- HL. apply YA0d.Z_to_le_bytes_to_Z.
Qed.

Lemma srx_le4_back : forall bs : list byte, length bs = 4%nat -> lib.Lib.Mem.le4 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold lib.Lib.Mem.le4, le_bytes_to_word. try unfold word_to_le_bytes.
pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as HB. rewrite HL in HB.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HB.
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
rewrite <- HL. apply YA0d.Z_to_le_bytes_to_Z.
Qed.

Lemma srx_mbyte_restrict : forall (H : word -> bool) m a,
  mbyte segs (mrestrict H m) a = if H (Z_to_bv 64 a) then seg_rom segs (Z_to_bv 64 a) else mbyte segs m a.
Proof. intros H m a. unfold mbyte, mrestrict. destruct (H (Z_to_bv 64 a)); reflexivity. Qed.

Lemma srx_aview_of_mbyte : forall (H : word -> bool) m m' a,
  mbyte segs m' a = mbyte segs m a -> aview segs H m' a = aview segs H m a.
Proof. intros H m m' a E. unfold aview. rewrite !srx_mbyte_restrict, E. reflexivity. Qed.

Lemma srx_aview_none : forall (H : word -> bool) m a,
  aview segs H m a = None <-> mbyte segs (mrestrict H m) a = None.
Proof. intros H m a. unfold aview. destruct (mbyte segs (mrestrict H m) a); cbn; split; congruence. Qed.

Lemma srx_rom_hidden : forall (W : world segs) x, w_H W x = true -> seg_rom segs x = None.
Proof.
intros W x Hx. pose proof (w_Hoff W x Hx) as F. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
rewrite F. reflexivity.
Qed.

Lemma srx_garr8_vis : forall (W : world segs) mem s l j, garr8 segs (mrestrict (w_H W) mem) s l ->
  (j < length l)%nat -> w_H W (Z_to_bv 64 (s + Z.of_nat j)) = false.
Proof.
intros W mem s l j G Hj. destruct (G j Hj) as [V _]. specialize (V 0%nat ltac:(lia)).
rewrite Z.add_0_r in V. rewrite srx_mbyte_restrict in V.
destruct (w_H W (Z_to_bv 64 (s + Z.of_nat j))) eqn:E; [|reflexivity].
rewrite (srx_rom_hidden W _ E) in V. discriminate V.
Qed.

Lemma srx_bytes_of_garr8 : forall (W : world segs) mem s l, garr8 segs (mrestrict (w_H W) mem) s l ->
  0 <= s -> s + Z.of_nat (length l) <= 2 ^ 64 -> lib.Lib.Mem.bytes_at segs mem s (map (Z_to_bv 8) l).
Proof.
intros W mem s l G H0 H1. split; [exact H0|]. split; [rewrite length_map; exact H1|].
intros i Hi. rewrite length_map in Hi. destruct (G i Hi) as [V R]. specialize (V 0%nat ltac:(lia)).
rewrite Z.add_0_r in V. rewrite srx_mbyte_restrict, (srx_garr8_vis W mem s l i G Hi) in V.
rewrite nth_error_map, (nth_error_nth' l 0 Hi). cbn [option_map].
change (lib.Lib.Mem.mrd segs mem (lib.Lib.Mem.wa (s + Z.of_nat i))) with (mbyte segs mem (s + Z.of_nat i)).
rewrite V. do 2 f_equal. match goal with |- ?F _ _ _ = _ => unfold F end.
rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact R.
Qed.

Lemma srx_stk_of_present : forall (H : word -> bool) mem lo hi,
  (forall a, lo <= a < hi -> apresent H mem a) -> 0 <= lo -> hi <= 2 ^ 64 -> lib.Lib.Frame.stk segs mem lo hi.
Proof.
intros H mem lo hi P H0 H1. split; [exact H0|]. split; [exact H1|].
intros a Ha. destruct (P a Ha) as [_ [b Hb]]. unfold lib.Lib.Mem.wa. split.
- unfold wview. rewrite Hb. discriminate.
- exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

Lemma srx_rw_C8 : forall m A, lib.Lib.Frame.stk segs m A (A + 8) ->
  exists w, lib.Lib.Step.rw_cells segs m A [lib.Lib.Cells.C8 w].
Proof.
intros m A ST. destruct (lib.Lib.Frame.stk_bytes segs m A (A + 8) ST ltac:(lia)) as (bs & L & Bt).
replace (Z.to_nat (A + 8 - A)) with 8%nat in L by lia.
exists (le_bytes_to_word bs). split; [split|].
- cbn. tauto.
- cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r, srx_le8_back by exact L. exact Bt.
- cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. destruct ST as (S1 & S2 & S3). split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (S3 (A + i) ltac:(lia))).
Qed.

Lemma srx_rw_C4 : forall m A, lib.Lib.Frame.stk segs m A (A + 4) ->
  exists w, lib.Lib.Step.rw_cells segs m A [lib.Lib.Cells.C4 w].
Proof.
intros m A ST. destruct (lib.Lib.Frame.stk_bytes segs m A (A + 4) ST ltac:(lia)) as (bs & L & Bt).
replace (Z.to_nat (A + 4 - A)) with 4%nat in L by lia.
exists (le_bytes_to_word bs). split; [split|].
- cbn. tauto.
- cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r, srx_le4_back by exact L. exact Bt.
- cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. destruct ST as (S1 & S2 & S3). split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (S3 (A + i) ltac:(lia))).
Qed.

Lemma srx_rw_C8_val : forall m A v, lib.Lib.Frame.stk segs m A (A + 8) ->
  (forall k, (k < 8)%nat -> mbyte segs m (A + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 8 k))) ->
  lib.Lib.Step.rw_cells segs m A [lib.Lib.Cells.C8 (Z_to_bv 64 v)].
Proof.
intros m A v ST V. destruct ST as (S1 & S2 & S3). split; [split|].
- cbn. tauto.
- cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. split; [exact S1|].
  split; [rewrite lib.Lib.Mem.length_le8; lia|].
  intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. rewrite srx_le8_nth by exact Hi. exact (V i Hi).
- cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (S3 (A + i) ltac:(lia))).
Qed.

Lemma srx_val_mem_C8 : forall (H : word -> bool) m e v,
  lib.Lib.Step.rw_cells segs m e [lib.Lib.Cells.C8 (Z_to_bv 64 v)] ->
  (forall k, (k < 8)%nat -> H (Z_to_bv 64 (e + Z.of_nat k)) = false) ->
  val_mem segs (mrestrict H m) e 8 v.
Proof.
intros H m e v RW Hv. destruct RW as [[_ [_ [_ Hb]]] _]. intros k Hk.
rewrite srx_mbyte_restrict, (Hv k Hk).
change (mbyte segs m (e + Z.of_nat k)) with (lib.Lib.Mem.mrd segs m (lib.Lib.Mem.wa (e + Z.of_nat k))).
rewrite Hb.
- cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact (srx_le8_nth v k Hk).
- cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r, lib.Lib.Mem.length_le8. exact Hk.
Qed.

Lemma srx_mbyte_of_rom_view : forall (H : word -> bool) m a b,
  H (Z_to_bv 64 a) = false ->
  aview segs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)) ->
  seg_rom segs (Z_to_bv 64 a) = Some b -> mbyte segs m a = Some b.
Proof.
intros H m a b Hv E R. unfold aview in E. rewrite srx_mbyte_restrict, Hv, R in E. cbn [option_map] in E.
destruct (mbyte segs m a) as [b'|]; [|discriminate E]. injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Definition srx_cell_b (a : Z) : bool :=
  match find_segment segs a 1 with Some _ => true | None => false end &&
  match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end &&
  match seg_rom segs (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition srx_cells_b (lo : Z) (n : nat) : bool := forallb (fun i => srx_cell_b (lo + Z.of_nat i)) (seq 0 n).
Definition srx_rom_val_b (a v : Z) : bool :=
  match seg_rom segs (Z_to_bv 64 a) with Some b => Z.eqb (bv_unsigned b) (v mod 256) | None => false end.
Definition srx_got_b (lo v : Z) : bool := forallb (fun k => srx_rom_val_b (lo + Z.of_nat k) (le_byte v 8 k)) (seq 0 8).

Lemma srx_cells_b_sound : forall lo n a, srx_cells_b lo n = true -> lo <= a < lo + Z.of_nat n -> srx_cell_b a = true.
Proof.
intros lo n a H Ha. unfold srx_cells_b in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat (a - lo))). rewrite in_seq in H.
replace (lo + Z.of_nat (Z.to_nat (a - lo))) with a in H by lia. apply H. lia.
Qed.

Lemma srx_got_b_sound : forall lo v k, srx_got_b lo v = true -> (k < 8)%nat ->
  seg_rom segs (Z_to_bv 64 (lo + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v 8 k)).
Proof.
intros lo v k H Hk. unfold srx_got_b in H. rewrite forallb_forall in H.
specialize (H k ltac:(apply in_seq; lia)). unfold srx_rom_val_b in H.
destruct (seg_rom segs (Z_to_bv 64 (lo + Z.of_nat k))) as [b|]; [|discriminate H].
apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H, Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. reflexivity.
Qed.

Lemma srx_cell_vis : forall (W : world segs) a, 0 <= a < 2 ^ 64 -> srx_cell_b a = true -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha Hc. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity].
pose proof (w_Hoff W _ E) as F. rewrite Z_to_bv_unsigned, bv_wrap_small in F by (unfold bv_modulus; cbn; lia).
unfold srx_cell_b in Hc. rewrite F in Hc. discriminate Hc.
Qed.

Lemma srx_cell_wv : forall m a, srx_cell_b a = true -> wview segs m (Z_to_bv 64 a) <> None.
Proof.
intros m a Hc. unfold srx_cell_b in Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc].
unfold wview in Hc |- *. cbv beta iota in Hc. destruct (m (Z_to_bv 64 a)); [discriminate|].
intros E. rewrite E in Hc. discriminate Hc.
Qed.

Lemma srx_cell_rom : forall a, srx_cell_b a = true -> seg_rom segs (Z_to_bv 64 a) <> None.
Proof.
intros a Hc. unfold srx_cell_b in Hc. apply andb_prop in Hc as [_ Hc]. intros E. rewrite E in Hc. discriminate Hc.
Qed.

Lemma srx_cell_img : forall a, srx_cell_b a = true -> in_img segs a.
Proof.
intros a Hc. unfold srx_cell_b in Hc. destruct (find_segment segs a 1) as [sg|] eqn:F; [|discriminate Hc].
destruct (find_segment_some_spec segs a 1 sg F) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

Lemma srx_stk_of_cells : forall m lo n, srx_cells_b lo n = true -> 0 <= lo -> lo + Z.of_nat n <= 2 ^ 64 ->
  lib.Lib.Frame.stk segs m lo (lo + Z.of_nat n).
Proof.
intros m lo n H H0 H1. split; [exact H0|]. split; [exact H1|]. intros a Ha.
pose proof (srx_cells_b_sound lo n a H Ha) as Hc. unfold lib.Lib.Mem.wa. split; [exact (srx_cell_wv m a Hc)|].
unfold lib.Lib.Mem.mrd. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
pose proof (srx_cell_rom a Hc) as Hr.
destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:R; [exists b; exact R | exfalso; exact (Hr eq_refl)].
Qed.

Definition srx_low_b : bool :=
  forallb (fun sg => (0 <=? Z.of_N (seg_base sg)) && (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? kLowMemEnd)) segs.
Lemma srx_segs_low : srx_low_b = true -> forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Proof.
intros H a (sg & Hin & Hr). unfold srx_low_b in H. rewrite forallb_forall in H. specialize (H sg Hin).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
End h.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable I : strtod_img.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition aj_memnorm (mem : word -> option byte) : Prop :=
  lib.Lib.Mem.mem_inv segs mem /\ MemNorm.task_mem segs mem.

Definition strtod_site_x (W : world segs) (mem : word -> option byte) (s e : Z) (txt : list Z) : Prop :=
  (s + Z.of_nat (length txt) + 1 <= si_img_lo I \/ si_globals_top I <= s) /\
  si_globals_top I <= e /\ e + 8 <= 2 ^ 62 /\
  (forall a, si_got_guard I <= a < si_got_guard I + 8 ->
     aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) /\
  aj_memnorm mem.

Definition astrtod_realizes_x (pc STKS : Z) (sm : list Z -> option (Z * Z)) (txt_ok : list Z -> Prop) : Prop :=
forall ly S Hp W regs mem md (s e : Z) (txt : list Z),
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + STKS <= spZ regs -> (forall a, spZ regs - STKS <= a < spZ regs -> apresent (w_H W) mem a) ->
alloc_ceiling <= ly_stk_lo ly -> ly_stk_hi ly <= 2 ^ 47 ->
getr regs 10 = w64 s -> getr regs 11 = w64 e ->
garr8 segs (rdW W mem) s (txt ++ [0]) -> txt_ok txt ->
4096 <= s -> s + Z.of_nat (length txt) + 1 <= 2 ^ 62 ->
(s + Z.of_nat (length txt) + 1 <= spZ regs - STKS \/ spZ regs <= s) ->
(forall a, e <= a < e + 8 -> apresent (w_H W) mem a /\ ~ aowned B ly S a /\ ~ in_img segs a) ->
0 <= e -> (e + 8 <= spZ regs - STKS \/ spZ regs <= e) -> (e + 8 <= s \/ s + Z.of_nat (length txt) + 1 <= e) ->
frm_zero (@YK11.fp_csr fx) ->
strtod_site_x W mem s e txt ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md' (bits c : Z),
c' = mkCfg (@YK11.mkst fx' regs' (w64 (raZ regs)) mem' (YK11.seg_rom segs)) md' /\
frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fx') (Z_to_bv 5 10) = Z_to_bv 64 bits /\
sm txt = Some (bits, c) /\ 0 <= c <= Z.of_nat (length txt) /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
val_mem segs (rdW W mem') e 8 (s + c) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e <= a < e + 8) -> ~ (spZ regs - STKS <= a < spZ regs) ->
   ~ (as_errno B <= a < as_errno B + 4) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - STKS <= a < spZ regs -> apresent (w_H W) mem' a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(aj_memnorm mem -> aj_memnorm mem')).

Section d.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.

Lemma strtod_end_of_frame : forall ly S Hp W mem md regs STKS cid pos e,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= e -> e + 8 <= frame_addr ly cid pos + fs_frame_bytes cid ->
  alloc_ceiling <= ly_stk_lo ly -> ly_stk_lo ly + STKS <= spZ regs ->
  (forall a, e <= a < e + 8 -> apresent (w_H W) mem a /\ ~ aowned B ly S a /\ ~ in_img segs a) /\
  0 <= e /\ (e + 8 <= spZ regs - STKS \/ spZ regs <= e).
Proof.
intros ly S Hp W mem md regs STKS cid pos e HAR Hin H1 H2 HC HS.
destruct (alx_frames segs B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & _ & Hb & _).
destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (F0 & Fc & _).
split; [|split; [lia | left; lia]].
intros a Ha. destruct (Hb a ltac:(lia)) as [Hp' Hno]. split; [exact Hp'|]. split; [exact Hno|].
exact (frm_img_x segs B ARx LAWS ly S Hp W mem md cid pos a HAR Hin ltac:(lia)).
Qed.

Hypothesis B_tp : as_tp B = si_tp I.
Hypothesis B_errno : as_errno B = si_errno I.
Hypothesis B_errno_own : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Hypothesis I_got : srx_got_b segs (si_got_guard I) (si_guard I) = true.
Hypothesis I_cells : srx_cells_b segs (si_got_guard I) 8 = true /\ srx_cells_b segs (si_guard I) 8 = true /\
  srx_cells_b segs (si_errno I) 4 = true.
Hypothesis I_ok : si_globals_top I <= alloc_ceiling /\
  0 <= si_got_guard I /\ si_got_guard I + 8 <= 2 ^ 62 /\ 0 <= si_guard I /\ si_guard I + 8 <= 2 ^ 62 /\
  0 <= si_errno I /\ si_errno I + 4 <= 2 ^ 62.
Variable pc : Z.
Variable sm0 : list Z -> option (Z * Z).
Hypothesis strtod_text : forall ainv aown, strtod_frame_g segs ainv aown -> strtod_contract_g segs I sm0 ainv aown pc.

Theorem astrtod_realizes_x_of : forall STKS sm txt_ok,
  si_k I <= STKS ->
  (forall txt, txt_ok txt -> Forall (fun c => FmtFp_facts3.is_numch c = true) txt /\ Z.of_nat (length txt) < 2 ^ 30) ->
  (forall txt bits c, txt_ok txt -> sm0 txt = Some (bits, c) -> sm txt = Some (bits, c)) ->
  astrtod_realizes_x pc STKS sm txt_ok.
Proof.
intros STKS sm txt_ok HK HTX HSM.
intros ly S Hp W regs mem md s e txt PRE HSTK HWIN HCEIL H47 Ha0 Ha1 GARR TOK Hs4 S62 HSW HE He0 HEW HES FRM SITE.
destruct PRE as (HAR & Hra & Hal & Hlo & Hhi & Hpres & Hgp & Htp).
unfold strtod_site_x, aj_memnorm in SITE.
destruct SITE as (SIMG & EG & E62 & GOTV & MI & TM).
destruct I_ok as (IG & G0 & G62 & Q0 & Q62 & R0 & R62).
destruct I_cells as (CG & CQ & CR).
destruct (HTX txt TOK) as (NUM & LEN).
pose proof asan_consts as (C1 & _).
assert (Hsp62 : spZ regs < 2 ^ 62) by lia.
assert (LT : length (txt ++ [0]) = (length txt + 1)%nat) by (rewrite length_app; cbn [length]; lia).
assert (VIS : forall a, strtod_vis_g I regs s e txt a -> w_H W (Z_to_bv 64 a) = false).
{ intros a [Ht | [[Hw | [He' | Hr]] | [Hg | Hq]]].
  - replace a with (s + Z.of_nat (Z.to_nat (a - s))) by lia.
    apply (srx_garr8_vis segs W mem s (txt ++ [0])); [exact GARR | rewrite LT; lia].
  - exact (proj1 (HWIN a ltac:(unfold YO0d.spZ in Hw; unfold spZ; lia))).
  - exact (proj1 (proj1 (HE a He'))).
  - apply (srx_cell_vis segs W a); [lia | exact (srx_cells_b_sound segs _ 4 a CR ltac:(lia))].
  - apply (srx_cell_vis segs W a); [lia | exact (srx_cells_b_sound segs _ 8 a CG ltac:(lia))].
  - apply (srx_cell_vis segs W a); [lia | exact (srx_cells_b_sound segs _ 8 a CQ ltac:(lia))]. }
set (aown := fun a => aowned B ly S a \/ w_H W (Z_to_bv 64 a) = true).
assert (HF : strtod_frame_g segs (ARx ly S Hp W) aown).
{ intros m0 d0 m1 d1 HA KEEP NN PG SBM.
  pose proof (same_but_materialized_wvb d0 d1 SBM) as Emd.
  eapply (alx_frame segs B ARx LAWS); [exact HA | | | | | |].
  - intros a Ha Ho. apply srx_aview_of_mbyte. exact (KEEP a Ha (or_introl Ho)).
  - intros a Hv Hn. apply Hv. apply srx_aview_none. apply srx_aview_none in Hn.
    rewrite srx_mbyte_restrict in Hn |- *. destruct (w_H W (Z_to_bv 64 a)); [exact Hn|].
    destruct (mbyte segs m0 a) eqn:E; [|reflexivity]. exfalso. apply (NN a); [rewrite E; discriminate | exact Hn].
  - rewrite Emd. destruct d0 as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct d0 as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct d0 as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - intros a Hband Hh. unfold w64 in Hh |- *.
    assert (Ha : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband; lia).
    pose proof (KEEP a Ha (or_intror Hh)) as K. unfold mbyte in K. rewrite (srx_rom_hidden segs W _ Hh) in K.
    destruct (m1 (Z_to_bv 64 a)), (m0 (Z_to_bv 64 a)); congruence. }
assert (STW : lib.Lib.Frame.stk segs mem (YO0d.spZ regs - si_k I) (YO0d.spZ regs)).
{ apply (srx_stk_of_present segs (w_H W)); [| unfold YO0d.spZ; unfold spZ in *; lia | unfold YO0d.spZ; unfold spZ in *; lia].
  intros a Ha. apply HWIN. unfold YO0d.spZ in Ha. unfold spZ. lia. }
assert (STE : lib.Lib.Frame.stk segs mem e (e + 8)).
{ apply (srx_stk_of_present segs (w_H W)); [intros a Ha; exact (proj1 (HE a Ha)) | lia | lia]. }
destruct (srx_rw_C8 segs mem e STE) as (ejunk & SLOT).
destruct (srx_rw_C8 segs mem (si_guard I) (srx_stk_of_cells segs mem _ 8 CQ ltac:(lia) ltac:(lia))) as (canary & QQ).
destruct (srx_rw_C4 segs mem (si_errno I) (srx_stk_of_cells segs mem _ 4 CR ltac:(lia) ltac:(lia))) as (ev & ERR).
assert (GG : lib.Lib.Step.rw_cells segs mem (si_got_guard I) [lib.Lib.Cells.C8 (Z_to_bv 64 (si_guard I))]).
{ apply (srx_rw_C8_val segs); [exact (srx_stk_of_cells segs mem _ 8 CG ltac:(lia) ltac:(lia))|].
  intros k Hk. pose proof (srx_cells_b_sound segs _ 8 (si_got_guard I + Z.of_nat k) CG ltac:(lia)) as Hc.
  apply (srx_mbyte_of_rom_view segs (w_H W)).
  - apply (srx_cell_vis segs W); [lia | exact Hc].
  - apply GOTV. lia.
  - exact (srx_got_b_sound segs _ _ k I_got Hk). }
eapply SRr_mono.
{ apply (strtod_text (ARx ly S Hp W) aown HF W regs mem md s e txt ejunk canary ev).
  - exact Ha0.
  - exact Ha1.
  - rewrite Htp. unfold w64. rewrite B_tp. reflexivity.
  - apply (srx_bytes_of_garr8 segs W); [exact GARR | lia | rewrite LT; lia].
  - exact NUM.
  - exact LEN.
  - exact SLOT.
  - exact STW.
  - unfold YO0d.spZ. unfold spZ in *. lia.
  - unfold YO0d.spZ. unfold spZ in *. lia.
  - exact Hs4.
  - exact S62.
  - unfold YO0d.spZ. unfold spZ in *. destruct HSW as [H1|H1]; [left; split; [exact SIMG | lia] | right; exact H1].
  - unfold YO0d.spZ. unfold spZ in *. destruct HEW as [H1|H1]; [left; split; lia | right; exact H1].
  - exact E62.
  - exact HES.
  - exact GG.
  - exact QQ.
  - exact ERR.
  - exact MI.
  - exact TM.
  - exact FRM.
  - exact VIS.
  - exact HAR.
  - intros a Hsc [Ho | Hh].
    + destruct Hsc as [Hw | [He' | Hr]].
      * apply (alx_stack segs B ARx LAWS ly S Hp W mem md a HAR); [unfold YO0d.spZ in Hw; unfold spZ in *; lia | exact Ho].
      * exact (proj1 (proj2 (HE a He')) Ho).
      * rewrite <- B_errno in Hr.
        pose proof (srx_cell_img segs a (srx_cells_b_sound segs _ 4 a CR ltac:(rewrite <- B_errno; lia))) as Hi.
        exact (B_errno_own a Hr (proj1 (alx_owned_image segs B ARx LAWS ly S Hp W mem md a HAR Hi) Ho)).
    + rewrite (VIS a (or_intror (or_introl Hsc))) in Hh. discriminate Hh. }
cbv beta. intros W' c' _ (-> & fx' & regs' & mem' & md' & Hc & FZ & bits & c & ev' & AI' & SBM & SC & Hc0 & FA0 & FOK
  & RP & RA & PEC & ERR' & KEEP & PG & WG & MI' & TM' & ST').
split; [reflexivity|]. exists fx', regs', mem', md', bits, c.
split.
{ rewrite Hc. unfold w64, raZ. rewrite Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [exact FZ|].
split.
{ intros r Hr. apply FOK; rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); lia. }
split.
{ rewrite <- FA0. f_equal. }
split; [exact (HSM txt bits c TOK SC)|].
split; [exact Hc0|].
split; [exact AI'|].
split; [intros r Hr; exact (RP r Hr)|].
split; [exact SBM|].
split.
{ apply (srx_val_mem_C8 segs); [exact PEC|]. intros k Hk. exact (proj1 (proj1 (HE (e + Z.of_nat k) ltac:(lia)))). }
split.
{ intros a Ha N1 N2 N3. apply srx_aview_of_mbyte. apply (proj1 (KEEP a Ha ltac:(
    unfold strtod_scratch_g, YO0d.spZ; unfold spZ in N2; rewrite B_errno in N3; intros [H1 | [H1 | H1]];
    [apply N2; lia | exact (N1 H1) | exact (N3 H1)]))). }
split.
{ intros a Ha. destruct (HWIN a Ha) as [Hv Hp']. split; [exact Hv | exact (PG a Hp')]. }
split.
{ intros a [Hv Hp']. split; [exact Hv | exact (PG a Hp')]. }
intros _. exact (conj MI' TM').
Qed.
End d.

Section l. Context {SK : YI16.sink_head}.
Variable PST : list (Z * Z).
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_img : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a.

Lemma ajournal_x_after_write_x : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
  AJ STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a \/
     (as_errno B <= a < as_errno B + 4)) ->
  ARx lyc Sc Hpc Wc memc' mdc' ->
  AJ STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr HJ Heqw Hgr Hsame HW HAR'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWf : forall a, wr_fp_frame FP S lyc a ->
  ~ aowned B lyc Sc a /\ ~ in_img segs a /\ 4096 <= a < alloc_ceiling /\
  (forall b n, In (b, n) (ablocks B lyc Sc) -> ~ (b <= a < b + req_size n))).
{ intros a (Hfp & cid & pos & Hin & Hr).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
  destruct (alx_frames segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & _).
  split; [exact (proj2 (Hfb a Hr))|].
  split; [exact (frm_img_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos a HAR HinC Hr)|].
  split; [zlia|].
  intros b n Hbin Hrb.
  pose proof (sep_block_frame_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b n cid pos HAR Hbin HinC) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
assert (HWe : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a /\ 0 <= a < kLowMemEnd).
{ intros a Ha. pose proof (errno_img a Ha) as Hi. exact (conj Hi (segs_low a Hi)). }
split; [exact HAR'|].
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros HWa.
  destruct (HW a HWa) as [Hw | [Hf | He]].
  - destruct (awr_byte_cases_x (SK := SK) segs B PST ARx LAWS STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a HJ Hw)
      as (_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]); [exact (Hs Hs') | zlia | zlia | zlia].
  - destruct (HWf a Hf) as (_ & _ & Hb & _). zlia.
  - destruct (HWe a He) as (_ & Hl). zlia. }
split.
{ intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
  destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
  apply Heqw; [zlia|]. intros HWa.
  destruct (HW _ HWa) as [Hw | [Hf | He]].
  - destruct (awr_byte_cases_x (SK := SK) segs B PST ARx LAWS STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k (p + i) HJ Hw)
      as (_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
    + zlia.
    + exact (Hnf Hfp).
    + assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
      pose proof (sep_blocks_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
    + assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
      pose proof (sep_block_frame_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
      unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
    + zlia.
  - exact (proj2 (proj2 (proj2 (HWf _ Hf))) p n H2 ltac:(zlia)).
  - destruct (HWe _ He) as (Hi' & _).
    exact (blk_img_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc p n (p + i) HAR H2 ltac:(zlia) Hi'). }
split.
{ intros a Hi Hns He Hpst Hsp. rewrite <- (F3 a Hi Hns He Hpst Hsp). pose proof (segs_low a Hi) as Hal'.
  apply Heqw; [zlia|]. intros HWa.
  destruct (HW a HWa) as [Hw | [Hf | He']].
  - destruct (awr_byte_cases_x (SK := SK) segs B PST ARx LAWS STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a HJ Hw)
      as (_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
    + zlia.
    + exact (blk_img_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b m a HAR Hbin Hr Hi).
    + assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
      unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
      exact (frm_img_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos a HAR Hin' Hr Hi).
    + zlia.
  - exact (proj1 (proj2 (HWf a Hf)) Hi).
  - exact (He He'). }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
  assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
  apply Heqw; [zlia|]. intros HWa.
  destruct (HW _ HWa) as [Hw | [Hf | He]].
  - destruct (awr_byte_cases_x (SK := SK) segs B PST ARx LAWS STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a HJ Hw)
      as (_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]).
    + zlia.
    + destruct Hr as [Hr | Hr]; [|zlia].
      pose proof (sep_block_frame_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
    + apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
      assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
      { eapply (sep_frames_pos_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
        rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
      destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc c' p' HAR
        ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
      pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
      pose proof (fs_frame_bytes_nonneg c') as Hnn'.
      destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
      * destruct Hr as [Hr | Hr]; [zlia | zlia].
      * destruct Hr as [Hr | Hr]; [zlia |].
        destruct Hd as [Hd | Hd].
        -- pose proof (shadow_mono _ _ Hd). zlia.
        -- pose proof (shadow_mono _ _ Hd). zlia.
  - exact (Hnf (proj1 Hf)).
  - destruct (HWe a He) as (Hi' & Hl). destruct Hr as [Hr | Hr].
    + exact (frm_img_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos a HAR HinC ltac:(rewrite Efa; exact Hr) Hi').
    + zlia. }
split; [exact Hgone|].
split; [intros a Ha; apply Hgr; apply Hpres, Ha|].
split; [exact Hstatic|]. split; [|exact HQT].
{ intros a HXa He. rewrite <- (F5 a HXa He).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
  assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
  pose proof (alx_extra segs B ARx LAWS lyc Sc Hpc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
  apply Heqw; [exact Ha64|]. intros HWa. exfalso.
  destruct (HW a HWa) as [Hw | [Hf | He']].
  - destruct (awr_byte_cases_x (SK := SK) segs B PST ARx LAWS STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a HJ Hw)
      as (_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]])]]).
    + apply Xs. rewrite Eslo, Eshi. zlia.
    + exact (Xb b m Hbin Hr).
    + assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
      unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
    + assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
      unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
  - destruct Hf as (_ & cid & pos & Hin & Hr).
    assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (proj1 (Xf cid pos HinC) Hr).
  - exact (He He'). }
Qed.

Definition aj_strtod_row (pc STKS : Z) (sm : list Z -> option (Z * Z)) (txt_ok : list Z -> Prop) : Prop :=
  forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k s e txt (o : Z) raw,
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
  getr regsT 10 = w64 s -> getr regsT 11 = w64 e ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> STKS - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  garr8 segs (rdW W memT) s (txt ++ [0]) -> txt_ok txt ->
  4096 <= s -> s + Z.of_nat (length txt) + 1 <= 2 ^ 62 ->
  (s + Z.of_nat (length txt) + 1 <= sp0 + o - STKS \/ sp0 + o <= s) ->
  (forall a, e <= a < e + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
  (e + 8 <= sp0 + o - STKS \/ sp0 + o <= e) -> (e + 8 <= s \/ s + Z.of_nat (length txt) + 1 <= e) ->
  frm_zero (@YK11.fp_csr fx) ->
  strtod_site_x W memT s e txt ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
  (fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2 (bits c : Z),
    c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
    LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fx') (Z_to_bv 5 10) = Z_to_bv 64 bits /\
    sm txt = Some (bits, c) /\ 0 <= c <= Z.of_nat (length txt) /\
    AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\
    val_mem segs (rdW W mem2) e 8 (s + c) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (e <= a < e + 8) -> ~ (sp0 + o - STKS <= a < sp0 + o) ->
       ~ (as_errno B <= a < as_errno B + 4) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
    aj_memnorm mem2).

Theorem aj_strtod_at_x : forall pc STKS sm txt_ok, astrtod_realizes_x pc STKS sm txt_ok -> ESTACK <= STKS ->
  aj_strtod_row pc STKS sm txt_ok.
Proof.
intros pc STKS sm txt_ok TXT HES W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k s e txt o raw
  HJ Ha0 Ha1 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw GARR TOK Hs4 S62 HSW HE HEW HSE FRM SITE.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
  split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
  split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
  split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (HE' : forall a, e <= a < e + 8 -> apresent (w_H W) memT a /\ ~ aowned B lyc Sc a /\ ~ in_img segs a).
{ intros a Ha. destruct (HE a Ha) as [Hw | Hf].
  - destruct (YGcallMx.awr_byte_present_x (SK := SK) segs B PST ARx LAWS STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k a HJ Hw)
      as [Hp' Hno].
    split; [exact Hp'|]. split; [exact Hno|].
    destruct (awr_byte_cases_x (SK := SK) segs B PST ARx LAWS STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k a HJ Hw)
      as (_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl _] _]])]]).
    + intros Hi. pose proof (segs_low a Hi). zlia.
    + exact (blk_img_x segs B ARx LAWS lyc Sc Hpc W memT mdc b m a HAR Hbin Hr).
    + assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
      unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
      exact (frm_img_x segs B ARx LAWS lyc Sc Hpc W memT mdc cid pos a HAR Hin' Hr).
    + intros Hi. pose proof (segs_low a Hi). zlia.
  - destruct Hf as (_ & cid & pos & Hin & Hr).
    assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    destruct (alx_frames segs B ARx LAWS lyc Sc Hpc W memT mdc cid pos HAR HinC) as (_ & _ & Hfb & _).
    destruct (Hfb a Hr) as [Hp' Hno]. split; [exact Hp'|]. split; [exact Hno|].
    exact (frm_img_x segs B ARx LAWS lyc Sc Hpc W memT mdc cid pos a HAR HinC Hr). }
assert (He0 : 0 <= e).
{ destruct (HE e ltac:(lia)) as [Hw | (_ & cid & pos & Hin & Hr)].
  - destruct (awr_byte_cases_x (SK := SK) segs B PST ARx LAWS STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k e HJ Hw)
      as (_ & [[Hc' _] | [((H0 & _) & _) | (cid & pos & _ & [((H0 & _) & _) | ((Hsl & _) & _)])]]); zlia.
  - assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
    destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc W memT mdc cid pos HAR HinC) as (Hf0 & _ & _).
    unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr. zlia. }
eapply SRr_mono.
{ exact (TXT lyc Sc Hpc W regsT memT mdc s e txt HPRE
    ltac:(rewrite Eslo, Hsp'; zlia)
    ltac:(intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia)
    ltac:(rewrite Eslo; exact Hceil) ltac:(rewrite Eshi; exact H47)
    Ha0 Ha1 GARR TOK Hs4 S62 ltac:(rewrite Hsp'; exact HSW) HE' He0 ltac:(rewrite Hsp'; exact HEW) HSE FRM SITE). }
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & bits & c & -> & FZ & FK & FA & SC & Hc0 & HAR2 & HP & Hsame
  & VM & Hfr & Hwin & Hgr & MN).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists fx', regs2, mem2, md2, bits, c.
split; [unfold raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact FZ|]. split; [exact FK|]. split; [exact FA|]. split; [exact SC|]. split; [exact Hc0|].
split.
{ eapply (ajournal_x_after_write_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
    (fun a => (e <= a < e + 8) \/ (sp0 + o - STKS <= a < sp0 + o) \/ (as_errno B <= a < as_errno B + 4)) HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right; left | right; right]; exact H'.
  - exact Hgr.
  - exact Hsame.
  - intros a [Ha | [Ha | Ha]].
    + destruct (HE a Ha) as [Hw | Hf]; [left; exact Hw | right; left; exact Hf].
    + left. unfold awr_byte. left. zlia.
    + right; right; exact Ha.
  - exact HAR2. }
split; [exact HP|]. split; [exact VM|]. split; [exact Hfr|]. split; [exact Hgr|].
exact (MN (proj2 (proj2 (proj2 (proj2 SITE))))).
Qed.
End l.
End t.
