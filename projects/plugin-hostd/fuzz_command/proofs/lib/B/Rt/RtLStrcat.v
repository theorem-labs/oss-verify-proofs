(* The strcat entry of fuzz_command.asan, lifted from the committed Bz-kit walk to our runtime contract
   (RtString.v astrcat_realizes). No function is proved here: the walk is the proof.
   - entry: PC 0x45220 is the trampoline `j 0x4c0ac` (the image's objdump listing, line 18791), stepped by
     B/Bz/A/I_tramp.v:33 tramp_strcat;
   - the interceptor body: B/Bz/A/I_strcatw.v:527 iscat_spec (depth 4432, :530), under its two Section hypotheses:
     rip_stmt = B/Bz/A/R_isPoisoned.v:296 rip_proof, and strcat_stmt = B/Bz/A/I_strcatww.v:56 sc_walk, which takes
     rip_stmt, strlen_stmt (B/Prog/wrap_kit_sl.v:21 sl_proof) and strcpy_stmt (B/Prog/strcpy_wrap_sc.v:20 sc_proof);
   - the glue: RtBzAdapt.v (our premises -> the walk's), RtBzClean.v (the walk run on the cleaned store, read at the
     call site), RtBzAdaptP.v art_post_clean (the walk's end state -> our art_post with the write set E).
   The walk WRITES [d + |dstr|, d + |dstr| + |str| + 1); the unwritten prefix [d, d + |dstr|) of the answer comes from
   the contract's own astr_at through art_post's "outside the window and E the view is kept" clause.

   Two premises of the contract were added for this walk (B's RtString.v:199 and :203):
   - the written range holds no read-only image byte below kLowMemEnd (:199): the walk writes through the cleaned
     store, which drops read-only addresses (RtBzClean.Dc), and awrite_ok's writable_at (RtDefs.v:46-47) holds at a
     read-only address whenever the store has a byte there; at or above the image's end Dc is false anyway
     (RtBzClean.Dc_above), so only the low band needs the premise (dc_dest below);
   - the destination tail does not start inside the source's last word (:203, aword_end): the walk takes the source
     with the slack that fills its terminator's 8-byte word (I_strcatw.v:536, :545) and asks that slack to be apart
     from the written range (I_strcatw.v:541-542). *)
(* The image-B twin of lib/A/Rt/RtLStrcat.v, for fuzz_command.asan-ubsan (no function proved): the B kit's
   walks (lib/B/Bz) and body proofs (lib/B/Prog), B's contract (lib/B/Rt/RtString.v), the B bridge and adapter, and
   every A address replaced by its B twin (each re-read from image B); the proof text is the A file's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YK1b YP03 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtBzHBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtBzStr.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strcatw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strcatww.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_tramp.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.wrap_kit_sl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.strcpy_wrap_sc.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module CW := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strcatw.
Module CWW := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strcatww.
Module TRP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_tramp.
Module RIP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.R_isPoisoned.
Module PSL := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.wrap_kit_sl.
Module PSC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.strcpy_wrap_sc.

(* ---- arithmetic ---- *)

Local Definition parked (P : Prop) : Prop := P.

Lemma amem_hi : forall p n, amem_range p n -> p + n <= 2 ^ 47.
Proof. intros p n H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H. lia. Qed.

Lemma lo_mod8 : forall sp, sp mod 16 = 0 -> (sp - 2 * ESTACK) mod 8 = 0.
Proof. intros sp H. unfold ESTACK. Z.div_mod_to_equations. lia. Qed.

Lemma word_end_le : forall e lo, e <= lo -> lo mod 8 = 0 -> e + (- e) mod 8 <= lo.
Proof. intros e lo H H8. Z.div_mod_to_equations. lia. Qed.

(* a range below an 8-aligned bound keeps its terminator's word below it *)
Lemma sep_slack : forall e n lo sp, lo mod 8 = 0 -> (e + n <= lo \/ sp <= e) ->
  e + (n + (- (e + n)) mod 8) <= lo \/ sp <= e.
Proof.
  intros e n lo sp H8 [H|H]; [left | right; exact H].
  pose proof (word_end_le (e + n) lo H H8). lia.
Qed.

Lemma ovl_slack : forall x n t, (t + n <= x \/ aword_end x n <= t) ->
  x + (n + (- (x + n)) mod 8) <= t \/ t + n <= x.
Proof. intros x n t [H|H]; [right; exact H | left; unfold aword_end in H; lia]. Qed.

(* the slack RtBzAdapt.bz_str_slack builds fills the terminator's word *)
Lemma tail_len : forall W mem p n,
  Z.of_nat (length (tail_bytes W mem (p + n))) = (- (p + (n + 1))) mod 8.
Proof. intros W mem p n. rewrite tail_bytes_length, <- mod_neg_succ, Z.add_assoc. reflexivity. Qed.

(* ---- the store the walk starts from and ends with ---- *)

(* a written byte is not a dropped address: below the image's end by the contract's read-only exclusion, above it
   because no segment reaches there *)
Lemma dc_low : forall a, 0 <= a < 2 ^ 47 -> ~ in_rom tfibsegs a -> RtBzClean.Dc (Z_to_bv 64 a) = false.
Proof.
  intros a Ha HN. apply RtBzClean.Dc_false.
  - destruct (BM.ro_addr BI.asegs (Z_to_bv 64 a)) eqn:E; [|reflexivity].
    exfalso. apply HN. pose proof (RtBzStr.ro_addr_in_rom _ E) as H.
    rewrite (RtBzPre.u64z a ltac:(lia)) in H. exact H.
  - rewrite (RtBzPre.u64z a ltac:(lia)). unfold BM.UTOP. lia.
Qed.

Lemma dc_dest : forall a, 0 <= a < 2 ^ 47 -> (a < kLowMemEnd -> ~ in_rom tfibsegs a) ->
  RtBzClean.Dc (Z_to_bv 64 a) = false.
Proof.
  intros a Ha HR. destruct (Z_lt_le_dec a TFIB_IMG_END) as [L|L].
  - apply dc_low; [exact Ha|]. apply HR. unfold TFIB_IMG_END, kLowMemEnd in *. lia.
  - apply RtBzClean.Dc_above. rewrite (RtBzPre.u64z a ltac:(lia)). unfold BM.UTOP. lia.
Qed.

(* the destination's current bytes, as the walk's rw_cells names them *)
Definition rd_bytes (m : word -> option byte) (a : Z) (n : nat) : list byte :=
  map (fun i => match BM.mrd BI.asegs m (BM.wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
      (seq 0 n).

Lemma rd_bytes_length : forall m a n, length (rd_bytes m a n) = n.
Proof. intros m a n. unfold rd_bytes. rewrite length_map, length_seq. reflexivity. Qed.

Lemma bytes_at_rd : forall m a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> BM.mrd BI.asegs m (BM.wa (a + Z.of_nat i)) <> None) ->
  BM.bytes_at BI.asegs m a (rd_bytes m a n).
Proof.
  intros m a n Ha Hn HR. split; [exact Ha|]. split; [rewrite rd_bytes_length; exact Hn|].
  intros i Hi. rewrite rd_bytes_length in Hi. unfold rd_bytes.
  rewrite nth_error_map, nth_error_seq.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  cbn [option_map Nat.add].
  destruct (BM.mrd BI.asegs m (BM.wa (a + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
  exfalso. exact (HR i Hi E).
Qed.

(* a byte the walk leaves in its stack window is in the store: the window is above the image *)
Lemma stk_some : forall (m : word -> option byte) lo hi a,
  BF.stk BI.asegs m lo hi -> TFIB_IMG_END <= lo -> lo <= a < hi -> m (Z_to_bv 64 a) <> None.
Proof.
  intros m lo hi a (Hlo & Hhi & ST) Himg Ha. destruct (ST a Ha) as (_ & b & Hb).
  unfold BM.mrd, BM.wa in Hb.
  destruct (m (Z_to_bv 64 a)) as [c|] eqn:E; [discriminate|].
  assert (HN : BPE.seg_rom BI.asegs (Z_to_bv 64 a) = None) by exact (seg_rom_none_high a ltac:(lia)).
  rewrite HN in Hb. discriminate.
Qed.

Section wv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a byte the image calls writable reads, on the visible store (A's file uses A/AFib.v writable_visible, which has
   no lib/B twin; this is the same fact on B's image, from its four segments all being readable) *)
Lemma tfibsegs_readable_b : forall sg, In sg tfibsegs -> seg_readable sg = true.
Proof.
  assert (H : forallb seg_readable tfibsegs = true) by (vm_compute; reflexivity).
  intros sg Hin. exact (proj1 (forallb_forall _ _) H sg Hin).
Qed.

Lemma writable_visible_b : forall (Hh : word -> bool) (m : word -> option byte) a, 0 <= a < 2 ^ 64 ->
  writable_at tfibsegs (mrestrict Hh m) a -> aview tfibsegs Hh m a <> None.
Proof.
  intros Hh m a Ra HW. unfold writable_at, wview in HW. unfold aview, mbyte.
  destruct (mrestrict Hh m (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate|].
  destruct (find_segment tfibsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:F; [|exfalso; exact (HW eq_refl)].
  destruct (seg_writable sg) eqn:Wr; [|exfalso; exact (HW eq_refl)].
  pose proof (find_segment_some_spec _ _ _ _ F) as (Hin & _ & _).
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite F, (tfibsegs_readable_b sg Hin).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) as [c|];
    [cbn; discriminate | exfalso; exact (HW eq_refl)].
Qed.
End wv.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the destination as the walk takes it: writable cells holding its current bytes, on the cleaned store *)
Lemma wr_dest_clean : forall stk ly S (W : world tfibsegs) regs mem a (n : nat),
  awrite_ok tfibsegs B stk ly S W regs mem a (Z.of_nat n) ->
  (forall j, a <= j < a + Z.of_nat n -> RtBzClean.Dc (Z_to_bv 64 j) = false) ->
  BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) a
    [BC.CB n (rd_bytes (RtBzClean.clean (mrestrict (w_H W) mem)) a n)].
Proof.
  intros stk ly S W regs mem a n (Ha & Han & Hn & HB & _) HD.
  assert (WV : forall j, a <= j < a + Z.of_nat n ->
            wview BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) (BM.wa j) <> None /\
            BM.mrd BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) (BM.wa j) <> None).
  { intros j Hj. destruct (HB j Hj) as (Wj & _ & _).
    rewrite (RtBzClean.wview_clean_nd (mrestrict (w_H W) mem) (BM.wa j) (HD j Hj)).
    rewrite (RtBzClean.mrd_clean_nd (mrestrict (w_H W) mem) (BM.wa j) (HD j Hj)).
    split; [exact Wj|].
    pose proof (writable_visible_b (w_H W) mem j ltac:(lia) Wj) as HV.
    unfold aview in HV. rewrite <- RtBzPre.mrd_mbyte in HV.
    intros E. rewrite E in HV. apply HV. reflexivity. }
  split; [split|].
  - cbn [BC.cells_wf BC.cell_wf]. split; [apply rd_bytes_length | exact I].
  - cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r. apply bytes_at_rd; [exact Ha | lia |].
    intros i Hi. exact (proj2 (WV (a + Z.of_nat i) ltac:(lia))).
  - cbn [BC.cells_size BC.csize]. rewrite Nat.add_0_r. split; [exact Ha|]. split; [lia|].
    intros i Hi. exact (proj1 (WV (a + i) ltac:(lia))).
Qed.

Hypothesis TB : CmdBSyms B.

Local Ltac c8 M := eapply (ro_c8 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M := eapply (ro_c1 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac roc RE H :=
  apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | exact H].
Local Ltac rwc RE H :=
  apply (RtBzClean.rw_cells_clean _ _ _ RE);
  [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity | exact H].

(* the strcat interceptor's fixed cells (I_strcatw.v:124), rows of the record's constant table (A/YF0m.v) *)
Lemma icells_cat_of_ARm : forall ly S H mem, ARm B ly S (aview tfibsegs H mem) -> CW.icells_cat (mrestrict H mem).
Proof.
  intros ly S H mem M. unfold CW.icells_cat.
  split; [c8 M|]. split; [c8 M|]. split; [c1 M|]. split; [c8 M|].
  split; [c1 M|]. split; [c1 M|]. split; [c8 M | c8 M].
Qed.

Lemma icells_cat_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> CW.icells_cat (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M.
  destruct (icells_cat_of_ARm ly S H mem M) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  split; [roc RE C1|]. split; [roc RE C2|]. split; [roc RE C3|]. split; [roc RE C4|].
  split; [roc RE C5|]. split; [roc RE C6|]. split; [roc RE C7 | roc RE C8].
Qed.

(* the runtime's "initialised" flag (asan_inited, 0xb1918), a writable cell *)
Lemma inited_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) ->
  BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict H mem)) 0xb1918 [BC.C1 (Z_to_bv 8 1)].
Proof.
  intros ly S H mem RE M.
  assert (C : BS.rw_cells BI.asegs (mrestrict H mem) 0xb1918 [BC.C1 (Z_to_bv 8 1)])
    by (apply rw_of_ro; [c1 M | vm_compute; reflexivity]).
  rwc RE C.
Qed.

End k.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.

Theorem cmd_strcat : astrcat_realizes tfibsegs B 0x45220.
Proof.
  unfold astrcat_realizes.
  intros ly S W regs mem md d x dstr str HPRE G10 G11 Hd Hx SD SX RDd AMd RDx AMx WRw AMw HRO TVd TVx SEP OVL HROM.
  unfold astr_len in *.
  lazymatch type of SEP with ?T => change (parked T) in SEP end.
  lazymatch type of OVL with ?T => change (parked T) in OVL end.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _ & HAL & _).
  assert (EST : ESTACK = 4096) by reflexivity.
  (* sizes and bands *)
  pose proof RDd as (_ & _ & SZd & RBd & _).
  pose proof RDx as (_ & _ & SZx & _ & _).
  pose proof WRw as (_ & _ & _ & WBw & _).
  pose proof (amem_hi _ _ AMd) as Bd.
  pose proof (amem_hi _ _ AMx) as Bx.
  pose proof (amem_hi _ _ AMw) as Bw.
  (* the stack *)
  destruct (stk_of_stk_pre B (2 * ESTACK) ly S W regs mem md HPRE ltac:(lia)) as (ST0 & HC0 & HCs & Hsp47).
  pose proof (lo_mod8 (spZ regs) HAL) as LO8.
  (* the read-only views and the cleaned store *)
  pose proof (rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 2 * ESTACK) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - 2 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  (* the two strings, with the bytes a word loop reads past each terminator *)
  destruct (bz_str_slack W mem d dstr SD TVd ltac:(lia) ltac:(unfold astr_len; lia)) as (DSm & DPAD).
  destruct (bz_str_slack W mem x str SX TVx ltac:(lia) ltac:(unfold astr_len; lia)) as (SXm & PAD).
  unfold astr_len in DSm, DPAD, SXm, PAD.
  pose proof (tail_len W mem d (Z.of_nat (length dstr))) as Ld.
  pose proof (tail_len W mem x (Z.of_nat (length str))) as Lx.
  assert (DS : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) d
                 (dstr ++ Z_to_bv 8 0 :: tail_bytes W mem (d + Z.of_nat (length dstr)))).
  { apply (bytes_at_clean _ d _ RE); [|exact DSm].
    rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, Nat2Z.inj_succ, Ld.
    pose proof (Z.mod_pos_bound (- (d + (Z.of_nat (length dstr) + 1))) 8 ltac:(lia)).
    unfold BM.UTOP. lia. }
  assert (SXc : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x
                  (str ++ Z_to_bv 8 0 :: tail_bytes W mem (x + Z.of_nat (length str)))).
  { apply (bytes_at_clean _ x _ RE); [|exact SXm].
    rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, Nat2Z.inj_succ, Lx.
    pose proof (Z.mod_pos_bound (- (x + (Z.of_nat (length str) + 1))) 8 ltac:(lia)).
    unfold BM.UTOP. lia. }
  (* the range checks *)
  assert (CKS : BQ.chk_ok (clean (mrestrict (w_H W) mem)) x (Z.of_nat (length str) + 1)).
  { apply (chk_ok_clean _ x _ RE); [lia | lia |].
    exact (chk_of_read (2 * ESTACK) W regs mem x (Z.of_nat (length str) + 1) (Z.of_nat (length str) + 1)
             (Z.of_nat (length str)) RDx AMx ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (CKD : BQ.chk_ok (clean (mrestrict (w_H W) mem)) d (Z.of_nat (length dstr))).
  { apply (chk_ok_clean _ d _ RE); [lia | lia |].
    exact (chk_of_read (2 * ESTACK) W regs mem d (Z.of_nat (length dstr) + 1) (Z.of_nat (length dstr))
             (Z.of_nat (length dstr)) RDd AMd ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (CKDk : BQ.chk_ok (clean (mrestrict (w_H W) mem)) d (Z.of_nat (length dstr) + 1)).
  { apply (chk_ok_clean _ d _ RE); [lia | lia |].
    exact (chk_of_read (2 * ESTACK) W regs mem d (Z.of_nat (length dstr) + 1) (Z.of_nat (length dstr) + 1)
             (Z.of_nat (length dstr)) RDd AMd ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (CKW : BQ.chk_ok (clean (mrestrict (w_H W) mem)) (d + Z.of_nat (length dstr)) (Z.of_nat (length str) + 1)).
  { apply (chk_ok_clean _ (d + Z.of_nat (length dstr)) _ RE); [lia | lia |].
    exact (chk_of_write B (2 * ESTACK) ly S W regs mem (d + Z.of_nat (length dstr)) (Z.of_nat (length str) + 1)
             (Z.of_nat (length str) + 1) (Z.of_nat (length str)) WRw AMw ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* the fixed cells *)
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_cat_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ICAT.
  pose proof (inited_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as AI.
  (* the destination: writable cells on the cleaned store *)
  assert (DCw : forall j, d + Z.of_nat (length dstr) <= j < d + Z.of_nat (length dstr) + Z.of_nat (Datatypes.S (length str)) ->
            RtBzClean.Dc (Z_to_bv 64 j) = false).
  { intros j Hj. apply dc_dest; [lia|]. intros Hl. apply HRO; [lia | exact Hl]. }
  assert (WRc : BS.rw_cells BI.asegs (clean (mrestrict (w_H W) mem)) (d + Z.of_nat (length dstr))
                  [BC.CB (Datatypes.S (length str))
                     (rd_bytes (clean (mrestrict (w_H W) mem)) (d + Z.of_nat (length dstr)) (Datatypes.S (length str)))]).
  { apply (wr_dest_clean B (2 * ESTACK) ly S W regs mem); [|exact DCw].
    rewrite Nat2Z.inj_succ. exact WRw. }
  (* separation from the callee's window *)
  pose proof (sep_of_read (2 * ESTACK) W regs mem x (Z.of_nat (length str) + 1) ltac:(lia) ltac:(lia) RDx) as SPx.
  pose proof (sep_of_read (2 * ESTACK) W regs mem d (Z.of_nat (length dstr) + 1) ltac:(lia) ltac:(lia) RDd) as SPd.
  pose proof (sep_of_write B (2 * ESTACK) ly S W regs mem (d + Z.of_nat (length dstr)) (Z.of_nat (length str) + 1)
                ltac:(lia) ltac:(lia) WRw) as SPw.
  lazymatch type of SPx with ?T => change (parked T) in SPx end.
  lazymatch type of SPd with ?T => change (parked T) in SPd end.
  lazymatch type of SPw with ?T => change (parked T) in SPw end.
  (* the run *)
  eapply (bz_run_clean B TB W 0x45220 regs mem md _ _ (romN_of_rt B W mem HROM)
            (rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - apply RtBzAdaptP.evt_grows. apply bz_canon. apply TRP.tramp_strcat.
    eapply (CW.iscat_spec RIP.rip_proof (CWW.sc_walk RIP.rip_proof PSL.sl_proof PSC.sc_proof))
      with (d := d) (p := x) (dstr := dstr) (dslack := tail_bytes W mem (d + Z.of_nat (length dstr)))
           (str := str) (slack := tail_bytes W mem (x + Z.of_nat (length str)))
           (junk := rd_bytes (clean (mrestrict (w_H W) mem)) (d + Z.of_nat (length dstr)) (Datatypes.S (length str)))
           (lo := spZ regs - 2 * ESTACK).
    + exact G10.
    + exact G11.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
    + unfold BR.kHighShadowEnd. lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact DS.
    + exact (proj2 SD).
    + exact SXc.
    + exact (proj2 SX).
    + exact WRc.
    + rewrite Lx. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
      exact (sep_slack x (Z.of_nat (length str) + 1) (spZ regs - 2 * ESTACK) (spZ regs) LO8 SPx).
    + rewrite Ld. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
      exact (sep_slack d (Z.of_nat (length dstr) + 1) (spZ regs - 2 * ESTACK) (spZ regs) LO8 SPd).
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold parked in SPw. lia.
    + rewrite Lx. unfold parked in OVL.
      destruct (ovl_slack x (Z.of_nat (length str) + 1) (d + Z.of_nat (length dstr))
                  ltac:(destruct OVL as [H|H]; [left; lia | right; exact H])) as [H|H];
        [left; exact H | right; lia].
    + unfold parked in SEP. lia.
    + exact DPAD.
    + exact PAD.
    + exact CKS.
    + exact CKD.
    + exact CKDk.
    + exact CKW.
    + exact AI.
    + exact ICAT.
    + exact M2S.
    + exact MI.
  - intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    unfold CW.iscat_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1' & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & ST'
                    & BYD & RWD & BYS).
    apply (art_post_clean B LAWS (2 * ESTACK) 4432 ly S W regs mem md _ _ _ ms' model' HPRE ltac:(lia)
             Hcl Heqv Hsbm).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + (* outside the window and the written range the walk kept the store *)
      intros y Hy HEy. exact (MU y (conj HEy (conj Hy I))).
    + (* the window's bytes are in the store *)
      intros a Ha.
      exact (stk_some m' (spZ regs - 2 * ESTACK) (spZ regs) a ST' ltac:(unfold TFIB_IMG_END; lia) ltac:(lia)).
    + exact GROW.
    + (* the written range: unowned, in the store, not dropped, not hidden *)
      intros a Ha. cbv beta in Ha.
      destruct (WBw a ltac:(lia)) as (Wa & Own & _).
      split; [exact Own|]. split; [lia|]. split.
      * apply dc_dest; [lia|]. intros Hl. apply HRO; [lia | exact Hl].
      * exact (wH_false_of_writable W mem a Wa).
    + (* the answer and the bytes the entry returns *)
      intros regs' mem' HR AVOUT AVE. split.
      * rewrite HR. reflexivity.
      * intros i Hi. rewrite !length_app in Hi. cbn [length] in Hi.
        destruct (Nat.lt_ge_cases i (length dstr)) as [Hlt|Hge].
        -- (* the unwritten prefix: the caller's string *)
           rewrite (AVOUT (d + Z.of_nat i) ltac:(lia)).
           ++ destruct SD as (SDb & _).
              rewrite (SDb i ltac:(rewrite length_app; cbn [length]; lia)).
              rewrite !app_nth1 by lia. reflexivity.
           ++ exact (proj2 (RBd (d + Z.of_nat i) ltac:(lia))).
           ++ cbv beta. lia.
        -- (* the written range: the walk's store *)
           rewrite (AVE (d + Z.of_nat i) ltac:(cbv beta; lia)).
           destruct BYD as (_ & _ & BYi).
           assert (Hi2 : (i < length (dstr ++ str ++ [BSh.z8]))%nat)
             by (rewrite !length_app; cbn [length]; lia).
           transitivity (option_map (fun b : byte => bv_unsigned b) (BM.mrd BI.asegs m' (BM.wa (d + Z.of_nat i))));
             [reflexivity|].
           rewrite (BYi i Hi2), (nth_error_nth' (dstr ++ str ++ [BSh.z8]) (Z_to_bv 8 0) Hi2).
           reflexivity.
Qed.

End s.
