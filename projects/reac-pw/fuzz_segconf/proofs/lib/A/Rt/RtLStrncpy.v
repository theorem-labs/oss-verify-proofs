(* Row 12 of the interceptor interface (provenance/evidence/interceptors/INTERFACE-A-interceptors.md): RtSeg.astrncpy_realizes at
   the strncpy trampoline 0x43ab4 of reac-pw/fuzz_segconf's ASan image A (`j 0x4b0fc`), lifted from the Bz-kit walks
   on the pattern of plugin-hostd/fuzz_command's lib/A/Rt/RtLStrcpy.v (origin/ossv/recipes):
   - the trampoline: one step (tramp_strncpyA below, I_tramp.v's tramp_step);
   - the wrapper and what it calls: A/Bz/A/I_strncpyw.v isncpy_spec, whose three Section hypotheses are discharged
     by A/Bz/A/R_isPoisoned.v rip_proof (the range check), A/FMmch.v mch_proof (musl memchr, under the memchr
     wrapper that musl strnlen calls) and A/Bz/A/I_stpncpyA.v stpncpyA_proof (musl strncpy and __stpncpy, whose
     padding goes through the memset wrapper; its own two hypotheses: rip_proof and A/RT_mem_bz.v ms_callZ_proof);
     the walks follow pupnp/FuzzHttp's lib/A0/ICP/I_strncpy.v, M_stpncpy.v, M_strnlen.v (origin/ossv/recipes),
     re-expressed in the Bz kit and generalized to the row's source (the first min (n, len + 1) bytes) and n < 2^32;
   - the bridge: the walk runs on the cleaned store (RtBzClean.bz_run_clean); its premises come from the contract
     through RtBzAdapt (strings with the word loop's slack, range checks, the stack window), RtBzPre (the runtime's
     fixed cells, read from the constant table of A/AF0m.v) and the ownership of those cells (the destination is
     not owned, A/AF0m.v Tfib_owned_static holds every cell the memset wrapper reads after the copy); its end
     state gives art_post with the write set [d, d + n) through RtBzAdaptP.art_post_clean. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YK1b YP03 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import
RtDefs RtBzHBase RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP SegRtPC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtBzStr RtString RtSeg.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_ncpyspec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_strncpyw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_stpncpyA.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_tramp.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memsetw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMmch.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.RT_mem_bz.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module NSP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_ncpyspec.
Module SNW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_strncpyw.
Module SPA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_stpncpyA.
Module TRP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_tramp.
Module MCW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memchrw.
Module MSW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memsetw.
Module RIP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.R_isPoisoned.
Module MCHP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMmch.
Module RMB := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.RT_mem_bz.

(* ---- the trampoline: one `j` to the wrapper ---- *)
Lemma tramp_strncpyA : TRP.tramp_step PC_strncpy SNW.i_strncpy.
Proof. unfold PC_strncpy, SNW.i_strncpy. TRP.tramp_proof. Qed.

(* ---- arithmetic ---- *)

(* the rounded end is the end of the string with its terminator and the slack after it *)
Lemma aword_end_succ : forall p k, RtString.aword_end p (k + 1) = p + k + 1 + (7 - (p + k) mod 8).
Proof.
  intros p k. unfold RtString.aword_end. replace (p + (k + 1)) with (p + k + 1) by lia.
  rewrite mod_neg_succ. lia.
Qed.

Lemma aword_end_ge : forall p k, p + k <= RtString.aword_end p k.
Proof. intros p k. unfold RtString.aword_end. pose proof (Z.mod_pos_bound (- (p + k)) 8 ltac:(lia)). lia. Qed.

(* the contracts' band room keeps a range below 2^47 *)
Lemma amem_top : forall p n, amem_range p n -> p + n <= 2 ^ 47.
Proof. intros p n H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H. lia. Qed.

(* ---- the bytes strncpy leaves: the walk's stpn_result is the row's ---- *)
Lemma stpn_result_row : forall (s : list byte) (n : nat),
  NSP.stpn_result s n = firstn n s ++ repeat (Z_to_bv 8 0) (n - length s).
Proof.
  intros s n. unfold NSP.stpn_result, NSP.stpn_k.
  destruct (Nat.le_ge_cases (length s) n) as [L|L].
  - rewrite Nat.min_l by exact L. rewrite firstn_all, firstn_all2 by exact L. reflexivity.
  - rewrite Nat.min_r by exact L. replace (n - n)%nat with 0%nat by lia. replace (n - length s)%nat with 0%nat by lia.
    reflexivity.
Qed.

(* ---- the destination as the walk reads it (RtLStrcpy.v's lemmas, for this image) ---- *)

Section d. Context {fx : YK11.FPState}.

Lemma tfib_segs_readable : forall sg, In sg tfibsegs -> seg_readable sg = true.
Proof.
  assert (H : forallb seg_readable tfibsegs = true) by (vm_compute; reflexivity).
  intros sg Hin. exact (proj1 (forallb_forall _ _) H sg Hin).
Qed.

(* a byte the store may be written at is a byte the walks' reader finds: every writable segment of the image is
   readable *)
Lemma mrd_of_writable : forall (m : word -> option byte) a,
  writable_at tfibsegs m a -> BM.mrd BI.asegs m (Z_to_bv 64 a) <> None.
Proof.
  intros m a HW. unfold writable_at, wview in HW. unfold BM.mrd, BPE.seg_rom, memory_read.
  change BI.asegs with tfibsegs. change (Z.of_N 1) with 1.
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  destruct (find_segment tfibsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:F; [|exfalso; exact (HW eq_refl)].
  destruct (seg_writable sg) eqn:Wr; [|exfalso; exact (HW eq_refl)].
  pose proof (YK04.find_segment_some_spec _ _ _ _ F) as (Hin & _ & _).
  rewrite (tfib_segs_readable sg Hin). change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) as [c|];
    [cbn; discriminate | exfalso; exact (HW eq_refl)].
Qed.

End d.

(* a destination byte is not dropped by the cleaning: above the low band no segment covers it, and in the low band
   it is not a read-only image byte *)
Lemma dst_dc : forall a, 0 <= a < 2 ^ 47 -> (a < kLowMemEnd -> ~ in_rom tfibsegs a) -> Dc (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hro. pose proof (u64z a ltac:(lia)) as Eu.
  destruct (Z_lt_le_dec a kLowMemEnd) as [L|L].
  - apply Dc_false; [| rewrite Eu; unfold BM.UTOP; lia].
    destruct (BM.ro_addr BI.asegs (Z_to_bv 64 a)) eqn:E; [|reflexivity].
    exfalso. apply (Hro L). rewrite <- Eu. exact (RtBzStr.ro_addr_in_rom _ E).
  - apply Dc_above. rewrite Eu. unfold TFIB_IMG_END, BM.UTOP, kLowMemEnd in *. lia.
Qed.

(* bytes that are present and writable are a block of cells the walk may write *)
Lemma rw_cb_of_present : forall (m : word -> option byte) (d : Z) (n : nat),
  0 <= d -> d + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> BM.mrd BI.asegs m (BM.wa (d + Z.of_nat i)) <> None /\
                           wview BI.asegs m (BM.wa (d + Z.of_nat i)) <> None) ->
  exists junk, BS.rw_cells BI.asegs m d [BC.CB n junk].
Proof.
  intros m d n Hd Hn H.
  exists (map (fun j => match BM.mrd BI.asegs m (BM.wa (d + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end)
             (seq 0 n)).
  split; [split|].
  - cbn [BC.cells_wf BC.cell_wf]. split; [rewrite length_map, length_seq; reflexivity | exact I].
  - cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
    split; [exact Hd|]. split; [rewrite length_map, length_seq; exact Hn|].
    intros i Hi. rewrite length_map, length_seq in Hi.
    rewrite nth_error_map, nth_error_seq.
    replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    cbn [option_map Nat.add].
    destruct (BM.mrd BI.asegs m (BM.wa (d + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
    exfalso. exact (proj1 (H i Hi) E).
  - split; [exact Hd|]. split; [cbn [BC.cells_size BC.csize]; lia|].
    intros i Hi. cbn [BC.cells_size BC.csize] in Hi.
    specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. exact (proj2 H).
Qed.

(* the walk's stack window is above the image, so every byte it leaves there is in the store *)
Lemma win_present : forall (m : word -> option byte) lo hi, BF.stk BI.asegs m lo hi -> TFIB_IMG_END <= lo ->
  forall a, lo <= a < hi -> m (Z_to_bv 64 a) <> None.
Proof.
  intros m lo hi (Hlo & Hhi & ST) Himg a Ha.
  destruct (ST a ltac:(lia)) as (_ & b & Hb). unfold BM.mrd, BM.wa in Hb.
  destruct (m (Z_to_bv 64 a)) as [c|] eqn:E; [discriminate|].
  assert (HN : BPE.seg_rom BI.asegs (Z_to_bv 64 a) = None) by exact (seg_rom_none_high a ltac:(lia)).
  rewrite HN in Hb. discriminate.
Qed.

(* ---- the range check of every tail [d + i, d + n) of a range the contract states ---- *)
Lemma chk_tail_of_shadow : forall (W : world tfibsegs) mem x n i,
  0 <= x -> x + n <= 2 ^ 63 -> 0 <= n < 2 ^ 32 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
  amem_range x (n + 8) -> 0 <= i <= n ->
  BQ.chk_ok (mrestrict (w_H W) mem) (x + i) (n - i).
Proof.
  intros W mem x n i Hx Hxn Hn HRA HV Ham Hi.
  pose proof Ham as Ham'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham'.
  destruct (Z.eq_dec (n - i) 0) as [E0|Hn0].
  - rewrite E0. split; [intros j Hj; lia|]. split; [intros Hq; lia | intros Hq; lia].
  - split; [|split].
    + apply (RtBzStr.acc_of_range_addressable (w_H W) mem (x + i) (n - i) ltac:(lia) ltac:(lia) ltac:(lia)).
      intros y Hy. apply HRA. lia.
    + apply (RtBzStr.qc_words_of_hull (w_H W) mem (x + i) (n - i) ltac:(lia) ltac:(lia) ltac:(lia)).
      apply RtBzStr.hull_of_shadow_hull_vis.
      intros s Hs. apply (HV ltac:(lia)). unfold shadow_addr in *.
      replace (x + i + (n - i) - 1) with (x + n - 1) in Hs by lia.
      assert (x / 8 <= (x + i) / 8) by (apply Z.div_le_mono; lia).
      assert ((SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + (x + i) / 8) / 8) by (apply Z.div_le_mono; lia).
      lia.
    + intros _. split; [| lia].
      apply (region_of_amem (x + i) (n - i) (n - i)); [lia | lia | lia |].
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
Qed.

(* ---- the cells the memset wrapper reads after the copy are runtime-owned (A/AF0m.v), so apart from any range
   the row lets strncpy write ---- *)
Lemma ncpy_cells_static : forall c, In c NSP.NCPY_CELLS ->
  0 < snd c /\ forall a, fst c <= a < fst c + snd c -> Exists (in_zr a) Tfib_owned_static.
Proof.
  (* decided byte by byte: a cell may span two adjacent owned ranges *)
  assert (C : forallb (fun c : Z * Z => (0 <? snd c) &&
                forallb (fun i => existsb (fun r : Z * Z => (fst r <=? fst c + Z.of_nat i) && (fst c + Z.of_nat i <? fst r + snd r))
                                    Tfib_owned_static)
                        (seq 0 (Z.to_nat (snd c))))
                NSP.NCPY_CELLS = true) by (vm_compute; reflexivity).
  intros c Hc. pose proof (proj1 (forallb_forall _ _) C c Hc) as X. cbv beta in X.
  apply andb_prop in X as (X0 & X1). apply Z.ltb_lt in X0. split; [exact X0|].
  intros a Ha.
  pose proof (proj1 (forallb_forall _ _) X1 (Z.to_nat (a - fst c)) ltac:(apply in_seq; lia)) as X2. cbv beta in X2.
  apply existsb_exists in X2 as (r & Hr & Hcov).
  apply andb_prop in Hcov as (H1 & H2). apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  rewrite Z2Nat.id in H1, H2 by lia.
  apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. lia.
Qed.

(* each of those cells lies in a segment of the image *)
Lemma ncpy_cells_img : forall c, In c NSP.NCPY_CELLS ->
  forall a, fst c <= a < fst c + snd c -> in_img tfibsegs a.
Proof.
  assert (C : forallb (fun c : Z * Z =>
                existsb (fun sg => (Z.of_N (seg_base sg) <=? fst c) &&
                                   (fst c + snd c <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs)
                NSP.NCPY_CELLS = true) by (vm_compute; reflexivity).
  intros c Hc a Ha. pose proof (proj1 (forallb_forall _ _) C c Hc) as X. cbv beta in X.
  apply existsb_exists in X as (sg & Hsg & Hcov).
  apply andb_prop in Hcov as (H1 & H2). apply Z.leb_le in H1, H2.
  exists sg. split; [exact Hsg | lia].
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : SegBSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* a range the contract lets strncpy write holds no byte of those cells: each is a runtime-owned image byte
   (A/AF0m.v Tfib_owned_static), and in the image the owned bytes are exactly those (AR_owned_image_law) *)
Lemma ncpy_apart_of_write : forall stk ly S (W : world tfibsegs) regs mem md d n,
  AR tfibsegs B ly S W mem md ->
  awrite_ok tfibsegs B stk ly S W regs mem d n -> NSP.ncpy_cells_apart d n.
Proof.
  intros stk ly S W regs mem md d n HAR (_ & _ & (Hn00 & _) & HB & _).
  unfold NSP.ncpy_cells_apart. destruct (Z.eq_dec n 0) as [E0|Hn0]; [left; exact E0| right].
  apply Forall_forall. intros c Hc.
  destruct (ncpy_cells_static c Hc) as (Hpos & Hown).
  destruct (Z_le_gt_dec (d + n) (fst c)) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (fst c + snd c) d) as [R|R]; [right; exact R|].
  exfalso.
  assert (Ha : d <= Z.max d (fst c) < d + n).
  { split; [apply Z.le_max_l|]. apply Z.max_lub_lt; [lia|]. apply Z.gt_lt in L. exact L. }
  assert (Hc' : fst c <= Z.max d (fst c) < fst c + snd c).
  { split; [apply Z.le_max_r|]. apply Z.max_lub_lt; [apply Z.gt_lt in R; exact R | lia]. }
  destruct (HB (Z.max d (fst c)) Ha) as (_ & HNo & _).
  apply HNo.
  apply (proj2 (al_owned_image _ _ LAWS ly S W mem md (Z.max d (fst c)) HAR (ncpy_cells_img c Hc _ Hc'))).
  rewrite (ts_owned B TB). exact (Hown _ Hc').
Qed.

Local Ltac c8 M := eapply (ro_c8 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M := eapply (ro_c1 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac roc RE H :=
  apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | exact H].
Local Ltac rwc RE H :=
  apply (RtBzClean.rw_cells_clean _ _ _ RE);
  [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity | exact H].

(* the strncpy wrapper's own cells (I_strncpyw.v icells_ncpy) *)
Lemma icells_ncpy_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> SNW.icells_ncpy (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M.
  assert (C1 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa2a48 [BC.C8 (Z_to_bv 64 0xa97f8)]) by c8 M.
  assert (C2 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa9815 [BC.C1 (Z_to_bv 8 1)]) by c1 M.
  assert (C3 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa4890 [BC.C8 (Z_to_bv 64 0x9ae88)]) by c8 M.
  assert (C4 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa48b0 [BC.C8 (Z_to_bv 64 0x9ad50)]) by c8 M.
  unfold SNW.icells_ncpy. split; [|split; [|split]].
  - roc RE C1.
  - roc RE C2.
  - roc RE C3.
  - roc RE C4.
Qed.

(* the memchr wrapper's cells (I_memchrw.v icells_mc) *)
Lemma icells_mc_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> MCW.icells_mc (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M.
  assert (C1 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa2a50 [BC.C8 (Z_to_bv 64 0xabff8)]) by c8 M.
  assert (C2 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa47a8 [BC.C8 (Z_to_bv 64 0x9a2f8)]) by c8 M.
  assert (C3 : BS.ro_cells BI.asegs (mrestrict H mem) 0xabff8 [BC.C8 (Z_to_bv 64 0x7fff8000)]) by c8 M.
  assert (C4 : BS.rw_cells BI.asegs (mrestrict H mem) 0xaccd8 [BC.C1 (Z_to_bv 8 1)])
    by (apply rw_of_ro; [c1 M | vm_compute; reflexivity]).
  unfold MCW.icells_mc. split; [|split; [|split]].
  - roc RE C1.
  - roc RE C2.
  - roc RE C3.
  - rwc RE C4.
Qed.

(* the memset wrapper's cells (I_memsetw.v icells_ms) *)
Lemma icells_ms_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> MSW.icells_ms (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M.
  assert (C1 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa2a50 [BC.C8 (Z_to_bv 64 0xabff8)]) by c8 M.
  assert (C2 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa35b8 [BC.C8 (Z_to_bv 64 0xaccd9)]) by c8 M.
  assert (C3 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa48e8 [BC.C8 (Z_to_bv 64 0x9a828)]) by c8 M.
  assert (C4 : BS.ro_cells BI.asegs (mrestrict H mem) 0xabff8 [BC.C8 (Z_to_bv 64 0x7fff8000)]) by c8 M.
  assert (C5 : BS.ro_cells BI.asegs (mrestrict H mem) 0xaccd9 [BC.C1 (Z_to_bv 8 1)]) by c1 M.
  unfold MSW.icells_ms. split; [|split; [|split; [|split]]].
  - roc RE C1.
  - roc RE C2.
  - roc RE C3.
  - roc RE C4.
  - roc RE C5.
Qed.

(* the asan-inited flag AsanInitFromRtl reads *)
Lemma inited_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) ->
  BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict H mem)) 0xaccd8 [BC.C1 (Z_to_bv 8 1)].
Proof.
  intros ly S H mem RE M.
  assert (C : BS.rw_cells BI.asegs (mrestrict H mem) 0xaccd8 [BC.C1 (Z_to_bv 8 1)])
    by (apply rw_of_ro; [c1 M | vm_compute; reflexivity]).
  rwc RE C.
Qed.

End k.

(* ---- the source as the walks state it: the bytes the copy reads ---- *)
(* With the NUL within the first n bytes: the string, its NUL and the slack to the end of the NUL's word (pupnp's
   form); else the first n bytes alone. Either way the bytes end at the row's aword_end, and they cover the
   min (n, len + 1) bytes the wrapper checks. *)
Lemma ncpy_source : forall (W : world tfibsegs) mem x s n,
  astr_at tfibsegs W mem x s -> atail_vis tfibsegs W mem (x + astr_len s) ->
  0 <= x -> x + astr_len s + 8 <= 2 ^ 47 -> 0 <= n ->
  RtBzClean.rom_eq (mrestrict (w_H W) mem) ->
  exists src,
    BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) x src /\
    NSP.ncpy_src x (Z.to_nat n) s src /\
    Z.min n (astr_len s + 1) <= Z.of_nat (length src) /\
    x + Z.of_nat (length src) <= RtString.aword_end x (Z.min n (astr_len s + 1)).
Proof.
  intros W mem x s n SX TAIL Hx Htop Hn RE.
  pose proof SX as (_ & NZ).
  destruct (bz_str_slack W mem x s SX TAIL Hx ltac:(lia)) as (BYm & PAD).
  set (sl := tail_bytes W mem (x + astr_len s)) in *.
  pose proof (tail_bytes_length W mem (x + astr_len s)) as SLL. fold sl in SLL.
  pose proof (Z.mod_pos_bound (x + astr_len s) 8 ltac:(lia)) as Hm.
  assert (BY : BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) x (s ++ Z_to_bv 8 0 :: sl)).
  { apply (bytes_at_clean _ x _ RE); [|exact BYm].
    rewrite length_app. cbn [length]. unfold astr_len in *. unfold BM.UTOP. lia. }
  unfold astr_len in *.
  destruct (Z_lt_le_dec (Z.of_nat (length s)) n) as [L|L].
  - exists (s ++ Z_to_bv 8 0 :: sl). split; [exact BY|]. split.
    + split; [exact NZ|]. left. exists sl. split; [reflexivity | exact PAD].
    + rewrite length_app. cbn [length]. rewrite Z.min_r by lia. rewrite aword_end_succ. lia.
  - exists (firstn (Z.to_nat n) s). split.
    + replace (s ++ Z_to_bv 8 0 :: sl) with (firstn (Z.to_nat n) s ++ (skipn (Z.to_nat n) s ++ Z_to_bv 8 0 :: sl)) in BY
        by (rewrite app_assoc, firstn_skipn; reflexivity).
      exact (proj1 (proj1 (BM.bytes_at_app BI.asegs _ x _ _) BY)).
    + split.
      * split; [exact NZ|]. right. split; [lia | reflexivity].
      * rewrite firstn_length_le by lia. rewrite Z.min_l by lia. rewrite Z2Nat.id by lia.
        pose proof (aword_end_ge x n). lia.
Qed.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

Theorem seg_strncpy : RtSeg.astrncpy_realizes tfibsegs B PC_strncpy.
Proof.
  unfold RtSeg.astrncpy_realizes.
  intros ly S W regs mem md d x n s HPRE G10 G11 G12 Hn Hd0 Hx0 SX RD AMx WR AMd HRO TAIL HSEP HROM.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _).
  pose proof WR as (_ & _ & _ & HWa & _).
  pose proof WR as (HWd & HWdn & HWn & _ & _ & HWRA & HWV).
  pose proof (amem_top x _ AMx) as Hx47.
  pose proof (amem_top d _ AMd) as Hd47.
  unfold astr_len in *.
  set (FS := Z.min n (Z.of_nat (length s) + 1)) in *.
  assert (FSb : 0 <= FS <= n /\ FS <= Z.of_nat (length s) + 1 /\ (0 < n -> 0 < FS)) by (unfold FS; lia).
  (* 1. the read-only views and the cleaned store *)
  pose proof (RtBzAdapt.rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  (* 2. the stack window, cleaned, cut to the walk's depth *)
  destruct (RtBzAdapt.stk_of_stk_pre B (2 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (HIMG0 : TFIB_IMG_END <= spZ regs - 2 * ESTACK) by (clear - HC0 HCs; unfold TFIB_IMG_END; lia).
  assert (STc : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 2 * ESTACK) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - 2 * ESTACK) (spZ regs));
      [exact HIMG0 | unfold BM.UTOP; lia | exact ST0]. }
  destruct (BF.stk_split BI.asegs _ _ (spZ regs - SNW.ISTRNCPY_DEPTH) _ STc ltac:(unfold ESTACK; lia))
    as (_ & ST).
  set (lo := spZ regs - SNW.ISTRNCPY_DEPTH) in *.
  assert (HIMG : TFIB_IMG_END <= lo) by (unfold lo; clear - HIMG0; unfold ESTACK in *; lia).
  (* 3. the source: the bytes the copy reads *)
  destruct (ncpy_source W mem x s n SX TAIL ltac:(lia) ltac:(unfold astr_len; lia) ltac:(lia) RE)
    as (src & BY & NS & SRC1 & SRC2).
  unfold astr_len in *. change (Z.min n (Z.of_nat (length s) + 1)) with FS in SRC1, SRC2.
  assert (SRC3 : x + Z.of_nat (length src) <= x + FS + 7).
  { unfold RtString.aword_end in SRC2. pose proof (Z.mod_pos_bound (- (x + FS)) 8 ltac:(lia)). lia. }
  (* 4. the separations: destination from source, both from the walk's window *)
  assert (OV : d + n <= x \/ x + Z.of_nat (length src) <= d) by (clear - HSEP SRC2; lia).
  clear HSEP.
  assert (SEPx : n = 0 \/ x + Z.of_nat (length src) <= lo \/ spZ regs <= x).
  { destruct (Z.eq_dec n 0) as [E0|Hn0]; [left; exact E0| right].
    pose proof (RtBzAdapt.sep_of_read (2 * ESTACK) W regs mem x FS ltac:(unfold ESTACK; lia) ltac:(lia) RD)
      as SR. unfold lo. clear - SR SRC3. unfold ESTACK in *. lia. }
  assert (SEPd : n = 0 \/ d + n <= lo \/ spZ regs <= d).
  { destruct (Z.eq_dec n 0) as [E0|Hn0]; [left; exact E0| right].
    pose proof (RtBzAdapt.sep_of_write B (2 * ESTACK) ly S W regs mem d n ltac:(unfold ESTACK; lia) ltac:(lia) WR)
      as SW. unfold lo. clear - SW. unfold ESTACK in *. lia. }
  (* 5. the destination: present and writable bytes of the cleaned store *)
  assert (DSTb : forall i, (i < Z.to_nat n)%nat ->
     BM.mrd BI.asegs (clean (mrestrict (w_H W) mem)) (BM.wa (d + Z.of_nat i)) <> None /\
     wview BI.asegs (clean (mrestrict (w_H W) mem)) (BM.wa (d + Z.of_nat i)) <> None).
  { intros i Hi.
    destruct (HWa (d + Z.of_nat i) ltac:(lia)) as (HW & _ & _).
    assert (DC : Dc (Z_to_bv 64 (d + Z.of_nat i)) = false).
    { apply dst_dc; [lia | intros Hlow; exact (HRO (d + Z.of_nat i) ltac:(lia) Hlow)]. }
    unfold BM.wa. rewrite (mrd_clean_nd _ _ DC), (wview_clean_nd _ _ DC).
    split; [exact (mrd_of_writable _ _ HW) | exact HW]. }
  destruct (rw_cb_of_present (clean (mrestrict (w_H W) mem)) d (Z.to_nat n) ltac:(lia) ltac:(lia) DSTb)
    as (junk & DST).
  (* 6. the range checks: min (n, len + 1) bytes at x, every tail of [d, d + n) *)
  assert (CKx : BQ.chk_ok (clean (mrestrict (w_H W) mem)) x FS).
  { apply (chk_ok_clean _ x _ RE); [lia | lia |].
    exact (RtBzAdapt.chk_of_read (2 * ESTACK) W regs mem x FS FS (Z.of_nat (length s)) RD AMx
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (CKd : NSP.chk_tails (clean (mrestrict (w_H W) mem)) d n).
  { intros i Hi. apply (chk_ok_clean _ (d + i) _ RE); [lia | lia |].
    exact (chk_tail_of_shadow W mem d n i HWd HWdn HWn HWRA HWV AMd Hi). }
  (* 7. the runtime's cells, and the destination apart from those the memset wrapper reads after the copy *)
  pose proof (ncpy_apart_of_write B TB LAWS (2 * ESTACK) ly S W regs mem md d n HAR WR) as APART.
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (inited_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as AI.
  pose proof (icells_ncpy_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ICN.
  pose proof (icells_mc_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ICM.
  pose proof (icells_ms_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ICS.
  (* 8. the run *)
  eapply (bz_run_clean B TB W PC_strncpy regs mem md _ _
            (RtBzAdapt.romN_of_rt B W mem HROM) (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - apply RtBzAdaptP.evt_grows. apply bz_canon. apply tramp_strncpyA.
    apply (SNW.isncpy_spec RIP.rip_proof MCHP.mch_proof (SPA.stpncpyA_proof RIP.rip_proof RMB.ms_callZ_proof))
      with (d := d) (s := x) (n := n) (str := s) (src := src) (junk := junk) (lo := lo).
    + exact G10.
    + exact G11.
    + exact G12.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold lo. lia.
    + unfold BR.kHighShadowEnd, lo. clear - HC0 HCs. unfold ESTACK in *. lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). exact Hsp47.
    + lia.
    + lia.
    + lia.
    + clear - SRC3 Hx47 FSb. lia.
    + lia.
    + exact BY.
    + exact NS.
    + exact DST.
    + exact OV.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). exact SEPx.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). exact SEPd.
    + exact CKx.
    + exact CKd.
    + exact APART.
    + exact M2S.
    + exact AI.
    + exact ICN.
    + exact ICM.
    + exact ICS.
    + exact MI.
  - intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Emsc & MU & _ & _ & ST' & CPY).
    apply (art_post_clean B LAWS (2 * ESTACK) SNW.ISTRNCPY_DEPTH ly S W regs mem md _ _ msc ms' model' HPRE);
      subst msc.
    + unfold ESTACK. lia.
    + exact Hcl.
    + exact Heqv.
    + exact Hsbm.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + (* outside the window and the destination the store is the caller's *)
      intros xw Hx HEx. change (m' xw = clean (mrestrict (w_H W) mem) xw).
      apply MU. cbn [BF.outside]. split; [exact HEx | split; [exact Hx | exact I]].
    + (* every byte of the window is in the store *)
      change (bv_unsigned (reg_get regs 2)) with (spZ regs) in ST'.
      exact (win_present m' _ _ ST' HIMG).
    + exact GROW.
    + (* the destination: unowned, in range, not dropped, not hidden *)
      intros a Ha. cbv beta in Ha.
      destruct (HWa a ltac:(lia)) as (HW & Hown & _).
      split; [exact Hown|]. split; [lia|]. split.
      * apply dst_dc; [lia | intros Hlow; exact (HRO a Ha Hlow)].
      * exact (wH_false_of_writable W mem a HW).
    + (* the answer and the bytes left at d *)
      intros regs' mem' HR _ HEv. split.
      * rewrite HR. reflexivity.
      * rewrite <- stpn_result_row.
        intros i Hi. rewrite NSP.stpn_result_length in Hi.
        rewrite (HEv (d + Z.of_nat i)) by (cbv beta; lia).
        destruct CPY as ((_ & BYc) & _). cbn [BC.cells_bytes BC.cbytes] in BYc. rewrite app_nil_r in BYc.
        destruct BYc as (_ & _ & BYc).
        assert (Hi' : (i < length (NSP.stpn_result s (Z.to_nat n)))%nat)
          by (rewrite NSP.stpn_result_length; exact Hi).
        transitivity (option_map (fun b : byte => bv_unsigned b) (nth_error (NSP.stpn_result s (Z.to_nat n)) i));
          [f_equal; exact (BYc i Hi') |].
        rewrite (nth_error_nth' (NSP.stpn_result s (Z.to_nat n)) (Z_to_bv 8 0) Hi'). reflexivity.
Qed.

End s.

(* ---- the closing form: the core's law proof discharges AR_laws, only the per-binary record remains ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.

Theorem seg_strncpy_closed : RtSeg.astrncpy_realizes tfibsegs B PC_strncpy.
Proof. exact (seg_strncpy B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

End closed.

Print Assumptions seg_strncpy_closed.
