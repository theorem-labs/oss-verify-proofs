(* fuzz_preset, slice S5b, lane VnumA (worker a Theorem Labs lane): ONE SEGMENT of parse_value in image A - the NUMBER ARM,
   listing rows 157..224 of the neutral per-function listing of the pinned rebuilt image A
   (parse_value's disassembly in the #102 pin A' image; row 1 is the entry 0x85f10), up to the SHARED JOIN at row 225.
   rule 24: no function is proved here. The segment's entry state is lane VproA's boundary VrdPro.vrd_disp_a,
   every callee is a published text or a named Section hypothesis, and the conclusion is the shared epilogue's
   boundary vrd_epi_a (defined here; lane WalkAlive's lib/A/VrdEpi.v proves the step from it to
   tparse_value_specX d's post).

   WHAT THE SEGMENT IS, instruction by instruction (addresses are image A's, offsets from parse_value's entry):
   - row 157 (+0x26c) `sb zero, 4(s8)`: unpoison the shadow byte of the 8-byte endptr local at the frame base
     fr + 0x20 (s8 = shadow_addr fr), the cell strtod writes;
   - rows 158..162: j = (b = '-') ? 1 : 0, s6 = p + j, the return value preset to -1, and the bound test
     s6 >= text + len -> refuse. The model's `match skipn j x with [] => jrefuse`;
   - rows 163..170: the first token byte must be a digit, else refuse (`if negb (digit c) then jrefuse`);
   - rows 171..182: a leading '0' followed by a digit refuses (`if (c =? 48) && digit c1 then jrefuse`);
   - rows 183..208: the token scan. The accepted set is the byte mask 2^58 + 2^26 + 13 shifted from '+' = 43,
     i.e. {'+','-','.','E','e'} (bits 0, 2, 3, 26, 58) together with the digits tested first: exactly
     PjGrammar.numch. The scan stops at the first byte outside it (rows 201/204 -> row 266) or at text + len
     (row 207 -> rows 266..267). s6 - p is then the token's length;
   - rows 266..270: the length is spilled at s1 + 0x18 and `jal -0xc18 <fuzz_malloc>` asks length + 1 bytes;
   - rows 271..282: the node's str field (v + 16) is shadow-checked and the block stored there; a NULL block
     refuses (row 277 -> the refusal join at row 324);
   - row 283 `jal -0x33f90 <__asan_memcpy>`: the token bytes into the block;
   - rows 284..294: the NUL at block + length;
   - rows 295..298: `jal 0x14b40 <strtod>` on the NUL-terminated token, with the endptr cell fr + 0x20 as a1;
   - rows 299..315: the double is stored at v + 8 (`fsd fa0, 0(a1)`, a1 = v + 8), the endptr must point at the
     token's NUL (rows 310..311), and `fclass.d` must report neither an infinity nor a NaN (mask 0x381), else
     refuse. This is the model's `whole txt` = (consumed = length txt) && finite bits;
   - rows 316..328: the type tag 3 (JNum) at v + 0, the cursor's p field advanced to s6, the endptr cell's
     shadow byte poisoned again, and the join into the shared tail;
   - rows 228..265: the shared epilogue - the frame header's retire word, the frame's shadow cleared (real-stack
     arm) or poisoned and the fake frame released by the flag store (side-stack arm), the callee-saved registers
     reloaded, and `ret`;
   - rows 329..374: every `errpath_load1` / `errpath_store*` call reached from this range is an ASan REPORT and is
     UNREACHABLE under the segment's shadow premises; each is discharged from them, never by a contract.

   WHAT IS A HYPOTHESIS HERE (rule 24): the three callees fuzz_malloc, __asan_memcpy and strtod.
   fuzz_malloc's contract is the tree's published text PRH_FnAlloc.tfuzz_malloc_specX, a premise of the
   statement. strtod is a Theorem Labs lane's published row (lib/Reusable/YStrtodRowX.v aj_strtod_at_x over
   lib/A/Prog/strtod_row.v strtod_row_aj_A), bound below as vrd_strtod_row at the frozen text's own model
   PRH_Reader.prh_jr_strtod. __asan_memcpy is the kit's intrinsic text with the memnorm keep
   (YGcallMxmn.aintrin_realizes_xm at OCpy), one named Section hypothesis of lib/A/VrdNumTail.v; preset's row for it
   is a Theorem Labs lane's lib/A/PRowCpy.v prow_asan_memcpy_xm_A, which the instance cites.

   THE GENERIC MEMORY INVARIANT (a Theorem Labs lane's 12:19Z ruling; the arm's twin of VrdArmStrOk.vrd_str_a_okP). REASON: an
   SRr post is opaque once Qed, so an end-state memory invariant must be in the segment's STATEMENT; the generic
   SRr_memnorm was measured NOT provable (a Theorem Labs lane), so it cannot be added afterwards. vrd_num_a_stmt_P is
   vrd_num_a_stmt with P and its laws (YC80x.srr_inv_laws, YSRrMemnorm.srr_inv_call / srr_inv_mn); the scan's
   segments vrd_seg_sa / vrd_seg_163 / vrd_loop have _P twins over YC1fPx's paj_run_x_inv / paj_run_to_x_inv, and
   each old statement survives BYTE-IDENTICAL as its corollary at P := fun _ => True. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a YK0j YN3v YG0s YP07 YP0a YG0p YP0d YP0c YC80 YImgTop YC1fP YC80x YC1fPx YC80xf
YGcallx YCbqGcall YGcallSx YGcallMx FCiface YStrtodRowX YFclsStep YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetFreeFo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog VrdPro.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import strtod_c strtod_row.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the pure model of the number arm (PjGrammar.v:272-300); no machine state ---- *)

(* the leading '-' the model skips before the first digit (PjGrammar.v:273) *)
Definition vrd_j (b : Z) : nat := if b =? 45 then 1%nat else 0%nat.

(* the model dispatches to jr_number exactly when the byte at the skipped cursor is none of the six it tests
   first (PjGrammar.v:293-299). The entry segment leaves that byte in a1, so this is the arm's selection. *)
Lemma vrd_jr_value_number : forall (sm : list Z -> Z * Z) (d : nat) (x : list Z) (b : Z) (y : list Z) ok,
  skip x = b :: y ->
  b <> 123 -> b <> 91 -> b <> 34 -> b <> 116 -> b <> 102 -> b <> 110 ->
  jr_value sm d x ok = jr_number sm (b :: y) ok.
Proof.
  intros sm d x b y ok Hs H123 H91 H34 H116 H102 H110.
  unfold jr_value. cbn [jrv]. rewrite Hs. cbv iota beta.
  destruct (Z.eqb_spec b 123); [contradiction|].
  destruct (Z.eqb_spec b 91); [contradiction|].
  destruct (Z.eqb_spec b 34); [contradiction|].
  destruct (Z.eqb_spec b 116); [contradiction|].
  destruct (Z.eqb_spec b 102); [contradiction|].
  destruct (Z.eqb_spec b 110); [contradiction|].
  reflexivity.
Qed.

(* rows 158..162: nothing left after the '-' (the bound test s6 >= text + len with j = 1, p + 1 = text + len) *)
Lemma vrd_num_refuse_short : forall sm b y ok,
  skipn (vrd_j b) (b :: y) = [] -> jr_number sm (b :: y) ok = (None, [], ok).
Proof.
  intros sm b y ok H. unfold jr_number, vrd_j in *. cbv zeta. rewrite H. reflexivity.
Qed.

(* rows 167..170: the first token byte is not a digit *)
Lemma vrd_num_refuse_nondigit : forall sm b y c z ok,
  skipn (vrd_j b) (b :: y) = c :: z -> digit c = false ->
  jr_number sm (b :: y) ok = (None, [], ok).
Proof.
  intros sm b y c z ok H Hd. unfold jr_number, vrd_j in *. cbv zeta. rewrite H. cbv iota beta.
  rewrite Hd. reflexivity.
Qed.

(* rows 171..182: a leading '0' with a digit after it *)
Lemma vrd_num_refuse_zero : forall sm b y c1 z ok,
  skipn (vrd_j b) (b :: y) = 48 :: c1 :: z -> digit c1 = true ->
  jr_number sm (b :: y) ok = (None, [], ok).
Proof.
  intros sm b y c1 z ok H Hd. unfold jr_number, vrd_j in *. cbv zeta. rewrite H. cbv iota beta.
  rewrite Hd. reflexivity.
Qed.

(* rows 183..330: the token is scanned, fuzz_malloc is called for its bytes plus one, and the outcome is
   whole txt (the endptr test of rows 310..311 and the fclass.d test of rows 312..315) *)
Lemma vrd_num_alloc : forall sm b y c z ok,
  skipn (vrd_j b) (b :: y) = c :: z -> digit c = true ->
  (c = 48 -> match z with c1 :: _ => digit c1 = false | [] => True end) ->
  jr_number sm (b :: y) ok =
    (let txt := firstn (vrd_j b) (b :: y) ++ c :: fst (span numch z) in
     let (ok0, ok1) := take ok in
     if ok0
     then (if whole sm txt
           then (Some (JNum txt (snd (sm txt)), snd (span numch z)), [EAlloc (S (length txt))], ok1)
           else (None, [EAlloc (S (length txt))], ok1))
     else (None, [EFail (S (length txt))], ok1)).
Proof.
  intros sm b y c z ok H Hd Hz. unfold jr_number, vrd_j in *. cbv zeta. rewrite H. cbv iota beta.
  rewrite Hd. cbn [negb]. cbv iota beta.
  replace ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end)%bool with false.
  2:{ destruct (Z.eqb_spec c 48) as [->|Hne]; [|reflexivity].
      cbn [andb]. destruct z as [|c1 z']; [reflexivity|]. symmetry. exact (Hz eq_refl). }
  cbv iota beta.
  destruct (span numch z) as [a r]. cbv iota beta zeta. cbn [fst snd].
  unfold jbind, jalloc, jret, jrefuse. cbv beta.
  destruct (take ok) as [ok0 ok1]. destruct ok0; cbv iota beta;
    [destruct (whole sm (firstn (if b =? 45 then 1%nat else 0%nat) (b :: y) ++ c :: a)); cbv iota beta|];
    cbn [app]; reflexivity.
Qed.

(* The token the code accepts, written as one function: an optional '-', one digit that is not a '0' followed
   by a digit, then the longest run of PjGrammar.numch. RESTATEMENT of pre338r2's PvDefs.num_tok
   (45cffb16b86), which is that branch's reading of the same rows; that branch is a reading aid only - it is
   in the old vocabulary and over the original images, and nothing of it is cited as evidence here. *)
Definition vrd_num_tok (x : list Z) : option (list Z * list Z) :=
  let j := match x with b :: _ => vrd_j b | [] => 0%nat end in
  match skipn j x with
  | [] => None
  | c :: z =>
    if negb (digit c) then None
    else if (c =? 48) && match z with c1 :: _ => digit c1 | [] => false end then None
    else let (a, r) := span numch z in Some (firstn j x ++ c :: a, r)
  end.

(* the whole number arm in one equation: the scan's outcome is vrd_num_tok, and the model's trace is the one
   allocation of the token's bytes plus one. This is the form the walk consumes. *)
Lemma vrd_num_tok_spec : forall sm b y ok,
  jr_number sm (b :: y) ok =
  match vrd_num_tok (b :: y) with
  | None => (None, [], ok)
  | Some (txt, r) =>
      let (ok0, ok1) := take ok in
      if ok0
      then (if whole sm txt
            then (Some (JNum txt (snd (sm txt)), r), [EAlloc (S (length txt))], ok1)
            else (None, [EAlloc (S (length txt))], ok1))
      else (None, [EFail (S (length txt))], ok1)
  end.
Proof.
  intros sm b y ok. unfold jr_number, vrd_num_tok, vrd_j. cbv zeta.
  destruct (skipn (if b =? 45 then 1%nat else 0%nat) (b :: y)) as [|c z]; [reflexivity|].
  destruct (negb (digit c)); cbv iota beta; [reflexivity|].
  destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end)%bool;
    cbv iota beta; [reflexivity|].
  destruct (span numch z) as [a r]. cbv iota beta zeta.
  unfold jbind, jalloc, jret, jrefuse. cbv beta.
  destruct (take ok) as [ok0 ok1]. destruct ok0; cbv iota beta;
    [destruct (whole sm (firstn (if b =? 45 then 1%nat else 0%nat) (b :: y) ++ c :: a)); cbv iota beta|];
    cbn [app]; reflexivity.
Qed.

(* ---- the scan's byte test, rows 197..204 ----
   The loop takes a byte when it is a digit (rows 198..199) or when bit (c - '+') of the constant the prologue
   builds in a5 is set (rows 187..191: 1 << 32, + 1, << 26, + 13 = 2^58 + 2^26 + 13 = 288230376218820621,
   bits 0, 2, 3, 26, 58 from '+' = 43, i.e. '+' '-' '.' 'E' 'e'). That set is exactly PjGrammar.numch.
   RESTATEMENT of pre338r2's parse_value_disp num5 / mask_num / numch_split (reading aid only; the constant
   and the shift base are re-read here from the listing rows). *)
Definition vrd_num5 (x : Z) : bool := (x =? 43) || (x =? 45) || (x =? 46) || (x =? 69) || (x =? 101).
Definition VRD_NUMMASK : Z := 288230376218820621.

Lemma vrd_nummask_bits : VRD_NUMMASK = 2 ^ 58 + 2 ^ 26 + 13.
Proof. reflexivity. Qed.

Lemma vrd_z256 : forall (f : Z -> bool) x, 0 <= x < 256 ->
  forallb f (map Z.of_nat (seq 0 256)) = true -> f x = true.
Proof.
  intros f x R A. rewrite forallb_forall in A. apply A.
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma vrd_numch_split : forall x, 0 <= x < 256 ->
  numch x = (digit x || ((43 <=? x) && (x <=? 101) && vrd_num5 x))%bool.
Proof.
  intros x R. apply Bool.eqb_prop.
  exact (vrd_z256 (fun z => Bool.eqb (numch z) (digit z || ((43 <=? z) && (z <=? 101) && vrd_num5 z))%bool)
           x R ltac:(vm_compute; reflexivity)).
Qed.

Lemma vrd_mask_num : forall x, 0 <= x < 256 -> 43 <= x <= 101 ->
  (Z.land (Z.shiftr VRD_NUMMASK ((x - 43) mod 64)) 1 =? 0) = negb (vrd_num5 x).
Proof.
  intros x R Hr. apply Bool.eqb_prop.
  pose proof (vrd_z256 (fun z => implb ((43 <=? z) && (z <=? 101))
            (Bool.eqb (Z.land (Z.shiftr VRD_NUMMASK ((z - 43) mod 64)) 1 =? 0) (negb (vrd_num5 z))))
            x R ltac:(vm_compute; reflexivity)) as H. cbv beta in H.
  replace ((43 <=? x) && (x <=? 101))%bool with true in H
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  exact H.
Qed.

(* ---- the pure facts of rows 312..315 (fclass.d and the mask 0x381 = 897): the class mask is zero exactly when
   the double is finite (neither an infinity nor a NaN), i.e. PjGrammar.finite. RESTATEMENT of the released plain
   lib/Prog/PvNum.v:191 pvn_fclass and :311 pvn_fclass_range (machine-state-free; restated, not imported, because
   PvNum.v loads the plain kit). ---- *)
Lemma vrd_fclass : forall x, (Z.land (fp_class fmt_double x) 897 =? 0) = finite x.
Proof.
  intros x. unfold fp_class, finite. cbv zeta.
  change (fp_exp_field fmt_double x) with (Z.land (Z.shiftr x 52) 2047).
  change (Z.ones (fp_ew fmt_double)) with 2047.
  destruct (Z.land (Z.shiftr x 52) 2047 =? 2047).
  - destruct (fp_man_field fmt_double x =? 0), (fp_sign_bit fmt_double x), (fp_is_snan fmt_double x); reflexivity.
  - destruct (Z.land (Z.shiftr x 52) 2047 =? 0), (fp_man_field fmt_double x =? 0), (fp_sign_bit fmt_double x);
      reflexivity.
Qed.

Lemma vrd_fclass_range : forall x, 0 <= fp_class fmt_double x < 1024.
Proof.
  intros x. unfold fp_class. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; rewrite ?Z.shiftl_1_l; lia.
Qed.

(* row 312 `fclass.d a0, fa0` is ONE step, lib/Reusable/YFclsStep.v fp_step_fclass_d (a working branch
   da73e1570f8, the settled home of the shared fclass step); this file's earlier twin vrd_fp_step_fclass is
   deleted in its favour. *)

(* b - '-' as an unsigned 64-bit word is nonzero for every byte but '-' itself: for b > 45 it is b - 45, and for
   b < 45 it wraps to 2 ^ 64 + b - 45. This is the `seqz a3, a1` of row 159, which the symbolic engine cannot fold
   below 45 (its range analysis loses the wrap). *)
Lemma vrd_sub45_ge1 : forall b, 0 <= b < 256 -> b <> 45 -> 1 <= zcanon (b + -45).
Proof.
intros b Hb Hne. unfold zcanon, M64.
destruct (Z_lt_ge_dec b 45) as [Hlt|Hge].
- rewrite <- (Z.mod_add (b + -45) 1 (2 ^ 64)) by lia.
  rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.


(* ---- the zeroed node is freeable at every depth with NO blocks: the refusals of rows 162, 170 and 182 happen
   before the arm writes one byte of v, so the None arm of the frozen post asks for exactly this
   (pj_fdR .. (MAXD - d) v []). Restatement, over PRH_Reader.v's R-names, of the released plain
   lib/Prog/PjStruct.v:598 pj_zero_node / :615 pj_zero_freeable (that file loads the plain kit, so it is not
   Required here). ---- *)
Lemma vrd_zero_val : forall (segs0 : list Segment) (m : word -> option byte) v a (w : nat),
  garr8 segs0 m v (repeat 0 56) -> v <= a -> a + Z.of_nat w <= v + 56 -> val_mem segs0 m a w 0.
Proof.
intros segs0 m v a w HG Ho Hw kk Hk.
replace (a + Z.of_nat kk) with (v + Z.of_nat (Z.to_nat (a - v + Z.of_nat kk))) by lia.
rewrite (garr8_mbyte segs0 m v (repeat 0 56) (Z.to_nat (a - v + Z.of_nat kk)) HG
  ltac:(rewrite repeat_length; lia)).
rewrite nth_repeat. f_equal. f_equal. unfold YO0f.le_byte. rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma vrd_zero_fd : forall (segs0 : list Segment) (m : word -> option byte) (lblk : Z -> Z -> Prop) v (n : nat),
  pj_rwR segs0 m v -> pj_zeroR segs0 m v -> pj_fdR segs0 m lblk n v [].
Proof.
intros segs0 m lblk v n Hrw Hz.
assert (HD : pj_hdrR segs0 m v 0 0 0 0 0 0 0).
{ unfold pj_hdrR, rd_u32, rd_u64. unfold pj_zeroR in Hz.
  split; [exact Hrw|].
  split; [split; [lia | exact (vrd_zero_val segs0 m v v 4 Hz ltac:(lia) ltac:(cbn; lia))]|].
  split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 8) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
  split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 16) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
  split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 24) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
  split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 32) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
  split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 40) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
  split; [lia | exact (vrd_zero_val segs0 m v (v + 48) 8 Hz ltac:(lia) ltac:(cbn; lia))]. }
assert (HS : forall (Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop), Pi false 0 0 0 [] ->
   pj_fshapeR segs0 m lblk Pi v []).
{ intros Pi HPi. split; [constructor|]. split; [intros bb x Hb; destruct Hb|].
  exists 0, 0, 0, 0, 0, 0, 0, false, [], [], [], [].
  split; [exact HD|].
  split; [left; split; reflexivity|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [apply Permutation_refl | exact HPi]. }
destruct n as [|n']; cbn [pj_fdR]; apply HS; [split; reflexivity | cbn [Z.to_nat pf_itemsR]; reflexivity].
Qed.

(* the frame lemma of a refused (freeable) tree, the companion of PRH_Reader.pj_nodeR_frame: a tree whose footprint
   (the node and the blocks it owns) keeps its bytes and writability is the same tree *)
Lemma vrd_fdR_frame : forall (sg : list Segment) (d : nat) m m' lblk p D,
  pj_fdR sg m lblk d p D -> pj_agreeR sg m m' (pj_footR p D) -> pj_fdR sg m' lblk d p D.
Proof.
intros sg d. induction d as [|d IH]; intros m m' lblk p D H HM; cbn [pj_fdR] in H |- *; unfold pj_fshapeR in H |- *;
  destruct H as (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Hh & Hs & Hk & Hy & HP & Hi);
  (split; [exact Hn|]); (split; [exact Ha|]);
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di;
  (split; [apply (pj_hdrR_frame sg m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]);
  (split; [exact Hs|]); (split; [exact Hk|]); (split; [exact Hy|]); (split; [exact HP|]).
- exact Hi.
- cbv beta in Hi |- *.
  assert (HinD : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HP) Hb)).
  assert (GEN : forall (j : nat) a ka D2,
     pf_itemsR sg m lblk (pj_fdR sg m lblk d) ks a ka j D2 ->
     (forall b, In b D2 -> In b D) ->
     (forall x, a <= x < a + 56 * Z.of_nat j -> pj_footR p D x) ->
     (ks = true -> forall x, ka <= x < ka + 8 * Z.of_nat j -> pj_footR p D x) ->
     pf_itemsR sg m' lblk (pj_fdR sg m' lblk d) ks a ka j D2).
  { induction j as [|j IHj]; intros a ka D2 H2 Hsub Hfa Hfk; cbn [pf_itemsR] in H2 |- *; [exact H2|].
    destruct H2 as (Dk2 & D1 & D3 & -> & Hkey & HP1 & Hrest).
    exists Dk2, D1, D3. split; [reflexivity|]. split.
    - unfold pj_keyR in Hkey |- *. destruct ks; [|exact Hkey].
      destruct Hkey as (x & Hx & Hor). exists x. split; [|exact Hor].
      apply (rd_u64_frame sg m m'); [exact Hx|]. intros y Hyy.
      assert (Hyy' : ka <= y < ka + 8 * Z.of_nat (S j)) by lia.
      exact (proj1 (HM y (Hfk eq_refl y Hyy'))).
    - split.
      + apply (IH m m' lblk a D1 HP1). intros x Hx. apply HM. destruct Hx as [Hx | (b & Hb & Hx)].
        * apply Hfa. lia.
        * right. exists b. split; [|exact Hx]. apply Hsub. apply in_or_app; right; apply in_or_app; left; exact Hb.
      + apply IHj; [exact Hrest | | |].
        * intros b Hb. apply Hsub. apply in_or_app; right; apply in_or_app; right; exact Hb.
        * intros x Hx. apply Hfa. lia.
        * intros Hks x Hx. apply (Hfk Hks). lia. }
  apply GEN; [exact Hi | | |].
  + intros b Hb. apply HinD. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb.
  + intros x Hx. destruct Hk as [(-> & -> & ->) | (k & _ & Hkn & ->)]; [cbn in Hx; lia|].
    right. exists (kids, k). split.
    * apply HinD. apply in_or_app; right; apply in_or_app; left; left; reflexivity.
    * unfold pj_holdsR; cbn [fst snd]. lia.
  + intros Hks x Hx. destruct Hy as [(_ & Hf & _) | (_ & k & _ & Hkn & ->)]; [rewrite Hks in Hf; discriminate Hf|].
    right. exists (keys, k). split.
    * apply HinD. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity.
    * unfold pj_holdsR; cbn [fst snd]. lia.
Qed.

(* ---- CAP's pj_ncapR (the kit's cut, PRH_Reader.v blob 4266e709561a, :243) survives a memory change that
   keeps a pj_nodeR tree's footprint pj_footR p D: every word pj_ncapR reads - the header's cap (p + 48) and kids
   (p + 24) words, and the same words of each item / member value, each in its 56-byte slot of the parent's kids
   block, which pj_nodeR puts in D whenever there is an item (n <= cap) - lies in that footprint. The companion of
   PRH_Reader.pj_nodeR_frame for the cut's new tree conjunct; the two list lemmas carry the induction hypothesis
   over the items / members, as pj_nodeR_frame's pj_itemsR_mono / pj_memsR_mono do. The kids word pj_ncapR names is
   the header's, by PjFoMember.pfm_rd_u64_det (one memory, one address). ---- *)
Lemma vrd_ncapR_items_frame : forall (sg : list Segment) m m' lblk (items : list jv) a Di,
  Forall (fun u => forall m m' lblk p D, pj_nodeR sg m lblk p u D -> pj_ncapR sg m p u ->
            pj_agreeR sg m m' (pj_footR p D) -> pj_ncapR sg m' p u) items ->
  pj_itemsR (pj_nodeR sg m lblk) a items Di -> pj_kidsR (pj_ncapR sg m) a items ->
  pj_agreeR sg m m' (fun x => (a <= x < a + 56 * Z.of_nat (length items)) \/ exists b, In b Di /\ pj_holdsR b x) ->
  pj_kidsR (pj_ncapR sg m') a items.
Proof.
intros sg m m' lblk items. induction items as [|u r IHr]; intros a Di HFa HI HK HA;
  cbn [pj_kidsR] in HK |- *; [exact I|].
inversion HFa as [|u0 r0 Hu Hr]; subst.
cbn [pj_itemsR] in HI. destruct HI as (D1 & D2 & -> & H1 & H2).
destruct HK as (K1 & K2). split.
- apply (Hu m m' lblk a D1 H1 K1). intros x Hx. apply HA. destruct Hx as [Hx | (b & Hb & Hx)].
  + left. cbn [length]. lia.
  + right. exists b. split; [apply in_or_app; left; exact Hb | exact Hx].
- apply (IHr (a + 56) D2 Hr H2 K2). intros x Hx. apply HA. destruct Hx as [Hx | (b & Hb & Hx)].
  + left. cbn [length]. lia.
  + right. exists b. split; [apply in_or_app; right; exact Hb | exact Hx].
Qed.

Lemma vrd_ncapR_mems_frame : forall (sg : list Segment) m m' lblk (members : list (list Z * jv)) a ka Di,
  Forall (fun mm => forall m m' lblk p D, pj_nodeR sg m lblk p (snd mm) D -> pj_ncapR sg m p (snd mm) ->
            pj_agreeR sg m m' (pj_footR p D) -> pj_ncapR sg m' p (snd mm)) members ->
  pj_memsR sg m lblk (pj_nodeR sg m lblk) a ka members Di ->
  pj_kidsR (fun a (mb : list Z * jv) => let (_, u) := mb in pj_ncapR sg m a u) a members ->
  pj_agreeR sg m m' (fun x => (a <= x < a + 56 * Z.of_nat (length members)) \/ exists b, In b Di /\ pj_holdsR b x) ->
  pj_kidsR (fun a (mb : list Z * jv) => let (_, u) := mb in pj_ncapR sg m' a u) a members.
Proof.
intros sg m m' lblk members. induction members as [|[nm u] r IHr]; intros a ka Di HFa HI HK HA;
  cbn [pj_kidsR] in HK |- *; [exact I|].
inversion HFa as [|mm0 r0 Hu Hr]; subst. cbn [snd] in Hu.
cbn [pj_memsR] in HI. destruct HI as (x & k & D1 & D2 & -> & _ & _ & H1 & H2).
destruct HK as (K1 & K2). split.
- refine (Hu m m' lblk a D1 H1 K1 _). intros y Hy. apply HA. destruct Hy as [Hy | (b & Hb & Hy)].
  + left. cbn [length]. lia.
  + right. exists b. split; [right; apply in_or_app; left; exact Hb | exact Hy].
- apply (IHr (a + 56) (ka + 8) D2 Hr H2 K2). intros y Hy. apply HA. destruct Hy as [Hy | (b & Hb & Hy)].
  + left. cbn [length]. lia.
  + right. exists b. split; [right; apply in_or_app; right; exact Hb | exact Hy].
Qed.

Lemma vrd_ncapR_frame : forall (sg : list Segment) t m m' lblk p D,
  pj_nodeR sg m lblk p t D -> pj_ncapR sg m p t -> pj_agreeR sg m m' (pj_footR p D) -> pj_ncapR sg m' p t.
Proof.
intros sg t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros m m' lblk p D HN HC HA; cbn [pj_ncapR] in HC |- *; try exact I.
- (* an array: the cap and kids words in the header, each item in its slot of the kids block *)
  cbn [pj_nodeR] in HN.
  destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & _ & _ & En & Hc & _ & Di & ED & Hi).
  destruct HC as (C48 & kids' & K24 & HK).
  pose proof Hh as (_ & _ & _ & _ & HK0 & _).
  rewrite (PjFoMember.pfm_rd_u64_det sg m (p + 24) kids' kids K24 HK0) in HK.
  assert (HW : forall a w, p <= a -> a + w <= p + 56 -> forall x, a <= x < a + w -> mbyte sg m' x = mbyte sg m x)
    by (intros a w H1 H2 x Hx; refine (proj1 (HA x _)); left; lia).
  split; [apply (rd_u64_frame sg m m' (p + 48) _ C48); apply (HW (p + 48) 8); lia|].
  exists kids. split; [apply (rd_u64_frame sg m m' (p + 24) kids HK0); apply (HW (p + 24) 8); lia|].
  apply (vrd_ncapR_items_frame sg m m' lblk items kids Di IH Hi HK).
  intros x Hx. apply HA. destruct Hx as [Hx | (b & Hb & Hx)].
  + right. exists (kids, 56 * cap).
    assert (Hp : 0 < cap) by (destruct items as [|u0 r0]; cbn [length] in Hx, En; lia).
    split; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity|].
    unfold pj_holdsR. cbn [fst snd]. lia.
  + right. exists b. split; [subst D; apply in_or_app; right; exact Hb | exact Hx].
- (* an object: the same, the values in the kids block's slots *)
  cbn [pj_nodeR] in HN.
  destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & _ & En & Hc & _ & Di & ED & Hi).
  destruct HC as (C48 & kids' & K24 & HK).
  pose proof Hh as (_ & _ & _ & _ & HK0 & _).
  rewrite (PjFoMember.pfm_rd_u64_det sg m (p + 24) kids' kids K24 HK0) in HK.
  assert (HW : forall a w, p <= a -> a + w <= p + 56 -> forall x, a <= x < a + w -> mbyte sg m' x = mbyte sg m x)
    by (intros a w H1 H2 x Hx; refine (proj1 (HA x _)); left; lia).
  split; [apply (rd_u64_frame sg m m' (p + 48) _ C48); apply (HW (p + 48) 8); lia|].
  exists kids. split; [apply (rd_u64_frame sg m m' (p + 24) kids HK0); apply (HW (p + 24) 8); lia|].
  apply (vrd_ncapR_mems_frame sg m m' lblk members kids keys Di IH Hi HK).
  intros x Hx. apply HA. destruct Hx as [Hx | (b & Hb & Hx)].
  + right. exists (kids, 56 * cap).
    assert (Hp : 0 < cap) by (destruct members as [|u0 r0]; cbn [length] in Hx, En; lia).
    split; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity|].
    unfold pj_holdsR. cbn [fst snd]. lia.
  + right. exists b. split; [subst D; apply in_or_app; right; exact Hb | exact Hx].
Qed.

(* ---- THE LEAF ARMS' FREE ORDER (the kit's cut 7cdbb61b5fa0, PRH_FnParse.v blob f0d92dcec7e9: tparse_value_specX's
   FREEORD-NONE conjunct in both arms of the result). At a value that is no container - the number arm, the string
   arm, a literal - the model's reader-side list prhPv_frees is PresetReqAt.lf of the value's own trace
   (PresetReqAt.v:270, jfv's leaf arm, at jr_value's fuel PjGrammar.v:319): the one block a leaf keeps, if any. And
   the node's order list is its block list, by PRH_PjOrder.pfo_leaf: the zeroed node (no block) or a node whose str is
   its one block. ---- *)
(* one step of jfv at prhPv_frees' fuel, by conversion (prhPv_frees spells the fuel Nat.succ, a constant, so cbn
   cannot unfold jfv) *)
Lemma vrd_frees_step : forall d x ok, prhPv_frees d x ok =
  match PjGrammar.skip x with
  | [] => []
  | b0 :: y0 =>
    if b0 =? 123 then PresetReqAt.jf_cont (PresetReqAt.jfl ReaderRes.jr_strtod (2 * length x)) d true (b0 :: y0) ok
    else if b0 =? 91 then PresetReqAt.jf_cont (PresetReqAt.jfl ReaderRes.jr_strtod (2 * length x)) d false (b0 :: y0) ok
    else PresetReqAt.lf (snd (fst (PjGrammar.jrv ReaderRes.jr_strtod (S (2 * length x)) d x ok)))
  end.
Proof. intros d x ok. reflexivity. Qed.

Lemma vrd_frees_leaf : forall d x ok b y, PjGrammar.skip x = b :: y -> b <> 123 -> b <> 91 ->
  prhPv_frees d x ok = PresetReqAt.lf (snd (fst (jr_value ReaderRes.jr_strtod d x ok))).
Proof.
intros d x ok b y Hs H1 H2. rewrite vrd_frees_step. unfold jr_value.
rewrite Hs, (proj2 (Z.eqb_neq b 123) H1), (proj2 (Z.eqb_neq b 91) H2). reflexivity.
Qed.

(* THE END-OF-TEXT ARM (VrdTop's vrd_eof_a_P): no value, no block *)
Lemma vrd_frees_eof : forall d x ok, PjGrammar.skip x = [] -> prhPv_frees d x ok = [].
Proof. intros d x ok Hs. rewrite vrd_frees_step, Hs. reflexivity. Qed.

(* THE CONTAINER ARM (VrdArmLC's, parse_items called at the opener b :: y): parse_value's list IS parse_items' at
   the opener. The fuels differ (jfv's 2 |x| inside, prhPi_frees' 2 |b :: y| + 2), and both cover the loop's text
   skip y, so they agree (PresetFreeFo.jf_fuel_mono, a Theorem Labs lane's fuel lemma the kit cites at PRH_FnParse.v:128) *)
Lemma vrd_frees_cont : forall d x ok b y (o : bool), PjGrammar.skip x = b :: y -> b = (if o then 123 else 91) ->
  prhPv_frees d x ok = prhPi_frees d o (b :: y) ok.
Proof.
intros d x ok b y o Hs Hb. rewrite vrd_frees_step, Hs. unfold prhPi_frees.
pose proof (PjGrammar.skip_len x) as Hlx. rewrite Hs in Hlx.
assert (HC : forall f, (2 * length (b :: y) <= f)%nat ->
    PresetReqAt.jf_cont (PresetReqAt.jfl ReaderRes.jr_strtod f) d o (b :: y) ok =
    PresetReqAt.jf_cont (PresetReqAt.jfl ReaderRes.jr_strtod (2 * length (b :: y))) d o (b :: y) ok).
{ intros f Hf. unfold PresetReqAt.jf_cont.
  match goal with |- (if ?t then _ else _) = _ => destruct t end; [reflexivity|].
  cbn [tl]. cbn [length] in Hf. pose proof (PjGrammar.skip_len y) as Hly.
  destruct (PjGrammar.skip y) as [|c r] eqn:Ey; try rewrite Ey in Hly; cbv beta iota zeta.
  - rewrite (proj2 (PresetFreeFo.jf_fuel_mono ReaderRes.jr_strtod (2 * length (@nil Z) + 2)) (S d) o 0%nat 0%nat []
      [] f ok) by (cbn [length] in *; lia).
    rewrite (proj2 (PresetFreeFo.jf_fuel_mono ReaderRes.jr_strtod (2 * length (@nil Z) + 2)) (S d) o 0%nat 0%nat []
      [] (2 * length (b :: y))%nat ok) by (cbn [length] in *; lia).
    reflexivity.
  - match goal with |- (if ?t then _ else _) = _ => destruct t end; [reflexivity|].
    rewrite (proj2 (PresetFreeFo.jf_fuel_mono ReaderRes.jr_strtod (2 * length (c :: r) + 2)) (S d) o 0%nat 0%nat []
      (c :: r) f ok) by (cbn [length] in *; lia).
    rewrite (proj2 (PresetFreeFo.jf_fuel_mono ReaderRes.jr_strtod (2 * length (c :: r) + 2)) (S d) o 0%nat 0%nat []
      (c :: r) (2 * length (b :: y))%nat ok) by (cbn [length] in *; lia).
    reflexivity. }
destruct o; cbn in Hb; subst b.
- rewrite Z.eqb_refl.
  rewrite (HC (2 * length x)%nat) by (cbn [length] in *; lia).
  rewrite (HC (2 * length (123%Z :: y) + 2)%nat) by (cbn [length] in *; lia). reflexivity.
- rewrite (proj2 (Z.eqb_neq 91 123) ltac:(lia)), Z.eqb_refl.
  rewrite (HC (2 * length x)%nat) by (cbn [length] in *; lia).
  rewrite (HC (2 * length (91%Z :: y) + 2)%nat) by (cbn [length] in *; lia). reflexivity.
Qed.

(* the zeroed node's header *)
Lemma vrd_zero_hdr : forall (segs0 : list Segment) (m : word -> option byte) v,
  pj_rwR segs0 m v -> pj_zeroR segs0 m v -> pj_hdrR segs0 m v 0 0 0 0 0 0 0.
Proof.
intros segs0 m v Hrw Hz. unfold pj_hdrR, rd_u32, rd_u64. unfold pj_zeroR in Hz.
split; [exact Hrw|].
split; [split; [lia | exact (vrd_zero_val segs0 m v v 4 Hz ltac:(lia) ltac:(cbn; lia))]|].
split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 8) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 16) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 24) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 32) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
split; [split; [lia | exact (vrd_zero_val segs0 m v (v + 40) 8 Hz ltac:(lia) ltac:(cbn; lia))]|].
split; [lia | exact (vrd_zero_val segs0 m v (v + 48) 8 Hz ltac:(lia) ltac:(cbn; lia))].
Qed.

(* the zeroed node's free order: no block, at any depth *)
Lemma vrd_zero_fo : forall (segs0 : list Segment) (m : word -> option byte) (lblk : Z -> Z -> Prop) v (n : nat),
  pj_rwR segs0 m v -> pj_zeroR segs0 m v -> PRH_PjOrder.pj_foR segs0 m lblk n v [] [].
Proof.
intros segs0 m lblk v n Hrw Hz.
apply (PRH_PjOrder.pfo_leaf segs0 m lblk n v 0 0 0 []).
- constructor.
- intros bb x Hb. destruct Hb.
- exact (vrd_zero_hdr segs0 m v Hrw Hz).
- left. split; reflexivity.
Qed.

(* a node whose one block is its str (the number arm's token copy, the string arm's block): its order list is that
   block, at any depth *)
Lemma vrd_str_fo : forall (segs0 : list Segment) (m : word -> option byte) (lblk : Z -> Z -> Prop) (n : nat) v ty num
    str k,
  pj_hdrR segs0 m v ty num str 0 0 0 0 -> lblk str k -> pj_apartR [(str, k)] v ->
  PRH_PjOrder.pj_foR segs0 m lblk n v [(str, k)] [(str, k)].
Proof.
intros segs0 m lblk n v ty num str k HH Hl Ha.
apply (PRH_PjOrder.pfo_leaf segs0 m lblk n v ty num str [(str, k)]).
- (* pfo_leaf's NoDup is stdpp's *)
  exact (list_relations.list.NoDup_singleton (str, k)).
- exact Ha.
- exact HH.
- right. exists k. split; [exact Hl | reflexivity].
Qed.

(* THE LIVE BYTES AT THE FIRST EVENT (PRH_Base.prh_live_at at j = 0) are the state's blocks_bytes: no event moved the
   entry's live requests yet (PresetReqAt.hlive_from_nil), and rs_live (room_of_cf S) is map snd (blocks S)
   (CfRoomLivePreset.rs_live_blocks is reflexivity), whose sum is blocks_bytes (a Theorem Labs lane's
   PresetLiveBytes.blocks_bytes_zsum, the same induction). So the per-event room's first conjunct is a leaf's
   `blocks_bytes S + request <= LIVE_MAX` (PRH_Base.v's note on prh_live_evs). *)
Lemma vrd_live_at0 : forall S E, prh_live_at S E 0 = blocks_bytes S.
Proof.
intros S E. unfold prh_live_at. cbn [firstn]. rewrite PresetReqAt.hlive_from_nil.
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)).
unfold blocks_bytes, blocks. rewrite map_map. cbn [snd].
induction (st_chunks S) as [|k l IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc k); cbn [map fold_right]; rewrite IH; reflexivity.
Qed.

(* ======================================================================================================== *)
(* THE SEGMENT, over the whole-program listing of image A (lib/A/PAImg_prog.v, PI_prog_A).                   *)
(* ======================================================================================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B prh_pst ARx).

(* listing offsets inside parse_value (image A, row r at 0x85f10 + 4 * (r - 2)) *)
Definition PV_NUM : Z := 0x26c.   (* row 157, A 0x8617c: the number arm's first instruction = VrdPro's VA_num *)
Definition PV_EPI : Z := 0x37c.   (* row 225, A 0x8628c: the shared epilogue, where every arm joins *)
Definition PV_REF : Z := 0x510.   (* row 326, A 0x86420: the number arm's own join, s5 already set *)
Definition PV_RET : Z := 0x41c.   (* row 265, A 0x8632c: ret *)

(* ---- THE SHARED EPILOGUE'S BOUNDARY, rows 225..265 (the split of record: VproA's measurement). Every arm
   joins at row 225: the string arm after setting s5 at rows 149..150, the container and literal arms through
   row 224 (`mv s5, a0`), and the number arm and every refusal through rows 326..328. At the join the arm has put
   its return value in s5 and has finished with the node and the cursor; what is left is the frame's retire
   word (row 227), the frame's 8 shadow bytes (rows 229..237), the fake frame's release (rows 238..239, through
   the flag word at F + 56) and the register reload (rows 249..265).
   The callee-saved registers are NOT asked here: at row 225 sp, s0, s3, s5 (at least) differ from the entry, and
   the epilogue's own loads restore them from the 13 spilled words (vrd_saved); the aregs_preserved of the FINAL
   registers is fpostWF's own conjunct, proved by the epilogue lemma.
   The arm's own result rides in RQ (any predicate of the allocator / memory state); the epilogue lemma asks of it
   only that it survive the tail's three writes and the frame's release. fx2 is the float state AT THE JOIN: an
   arm that returns from a callee which moved the f registers (the number arm, from strtod; the container arm,
   from parse_items) hands it in, and the Section's fx is parse_value's entry float state, which fregs_kept_x
   relates it to.
   THE BUDGET (the kit's cut 7cdbb61b5fa0, PRH_FnParse.v blob f0d92dcec7e9): tparse_value_specX's post is fpostWFbm at
   YCbqGwild.wbudget CW 0, the journal at a budget WS of wild traces with at most 0 outside the cursor set CW
   (parse_string's and parse_items' posts are at that budget, so the string and container arms cannot give the empty
   one). So the journal below is at a budget WS with wbudget CW 0 WS, ONE conjunct in the place of the old ajournal_x
   (at WS = [] it IS ajournal_x, YCbqG.v, and wbudget CW 0 [] holds: the number and literal arms, which store no wild
   trace). ---- *)
(* THE RE-HIDING MOVE: vrd_epi_aR is the join over a world relation R (its journal at ajournal_xwR R). The container
   and string arms reach row 225 after parse_items / parse_string, whose texts post their journal at wle' segs RZ_cf,
   so their join is at that relation. vrd_epi_a, below, is vrd_epi_aR at wle: every statement over it keeps its
   text. *)
Definition vrd_epi_aR (R : world segs -> world segs -> Prop) (fx2 : YK11.FPState) (d : nat) (CW : list (list Z))
  (e q v : Z) (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (pos rv : Z)
  (RQ : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Prop)
  : world segs -> config -> Prop :=
  fun W c => exists (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ly : alayout) (S : astate)
                    (Hp : list Z) (k : Z),
  c = mkCfg (@YK11.mkst fx2 regs (w64 (pa_sigma AS_parse_value + PV_EPI)) mem (YK11.seg_rom segs)) md /\
  (* the journal from parse_value's entry, at the caller-window stack of the frozen post, own frame still live, at a
     budget WS within the text's wbudget CW 0 *)
  (exists WS : list (list Z),
     ajournal_xwR (SK := SK) segs B prh_pst ARx R (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
       ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k WS /\
     YCbqGwild.wbudget CW 0 WS) /\
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W) mem a = aview segs (w_H W0) mem0 a) /\
  (* the registers the tail reads: s0 = the entry sp, s2 = s10 = the fake frame, s8 = its shadow, s5 = the
     return value; gp and tp are never written by any arm *)
  getr regs 8 = w64 (spZ regs0) /\
  getr regs 18 = w64 (frame_addr ly 0 pos) /\ getr regs 26 = w64 (frame_addr ly 0 pos) /\
  getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) /\ getr regs 21 = w64 rv /\
  getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\ YK0s.ret_ok (getr regs0 1) /\
  (* the 13 spilled words the tail reloads, and the flag word the release reads (row 238) *)
  vrd_saved (rdW W mem) (spZ regs0) regs0 /\
  val_mem segs (rdW W mem) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) /\
  (* the float state at the join against the entry's *)
  frm_zero (@YK11.fp_csr fx2) /\ fregs_kept_x fx fx2 /\
  RQ ly S Hp W mem.
Definition vrd_epi_a (fx2 : YK11.FPState) (d : nat) (CW : list (list Z)) (e q v : Z)
  (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (pos rv : Z)
  (RQ : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Prop)
  : world segs -> config -> Prop :=
  vrd_epi_aR (@wle segs) fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ.

(* ---- vrd_epi_aR, NAMED. ADDITIVE: the definition above is unchanged. vrd_epi_R names each conjunct of its body in
   the definition's order, at the witnesses regs mem md ly S Hp k; vrd_epi_R_of reads vrd_epi_aR into it and
   vrd_epi_aR_of_R builds vrd_epi_aR from it. ---- *)
Local Set Implicit Arguments.

Record vrd_epi_R (R : world segs -> world segs -> Prop) (fx2 : YK11.FPState) (d : nat) (CW : list (list Z))
  (e q v : Z) (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (pos rv : Z)
  (RQ : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Prop) (W : world segs) (c : config)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ly : alayout) (S : astate) (Hp : list Z) (k : Z)
  : Prop := {
  vepi_cfg : c = mkCfg (@YK11.mkst fx2 regs (w64 (pa_sigma AS_parse_value + PV_EPI)) mem (YK11.seg_rom segs)) md;
  vepi_jrn : exists WS : list (list Z),
    ajournal_xwR (SK := SK) segs B prh_pst ARx R (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
      ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k WS /\
    YCbqGwild.wbudget CW 0 WS;
  vepi_win : forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
    aview segs (w_H W) mem a = aview segs (w_H W0) mem0 a;
  vepi_s0 : getr regs 8 = w64 (spZ regs0);
  vepi_s2 : getr regs 18 = w64 (frame_addr ly 0 pos);
  vepi_s10 : getr regs 26 = w64 (frame_addr ly 0 pos);
  vepi_s8 : getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8);
  vepi_s5 : getr regs 21 = w64 rv;
  vepi_gp : getr regs 3 = getr regs0 3;
  vepi_tp : getr regs 4 = getr regs0 4;
  vepi_ra : YK0s.ret_ok (getr regs0 1);
  vepi_saved : vrd_saved (rdW W mem) (spZ regs0) regs0;
  vepi_flag : val_mem segs (rdW W mem) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos);
  vepi_frm : frm_zero (@YK11.fp_csr fx2);
  vepi_fregs : fregs_kept_x fx fx2;
  vepi_rq : RQ ly S Hp W mem }.

Lemma vrd_epi_R_of : forall R fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c,
  vrd_epi_aR R fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c ->
  exists regs mem md ly S Hp k,
    vrd_epi_R R fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c regs mem md ly S Hp k.
Proof.
intros R fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c H.
destruct H as (regs & mem & md & ly & S & Hp & k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 &
  H13 & H14 & H15 & H16).
exists regs, mem, md, ly, S, Hp, k.
exact {| vepi_cfg := H1; vepi_jrn := H2; vepi_win := H3; vepi_s0 := H4; vepi_s2 := H5; vepi_s10 := H6;
  vepi_s8 := H7; vepi_s5 := H8; vepi_gp := H9; vepi_tp := H10; vepi_ra := H11; vepi_saved := H12; vepi_flag := H13;
  vepi_frm := H14; vepi_fregs := H15; vepi_rq := H16 |}.
Qed.

Lemma vrd_epi_aR_of_R : forall R fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c regs mem md ly S Hp k,
  vrd_epi_R R fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c regs mem md ly S Hp k ->
  vrd_epi_aR R fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c.
Proof.
intros R fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c regs mem md ly S Hp k HR.
exists regs, mem, md, ly, S, Hp, k.
exact (conj (vepi_cfg HR) (conj (vepi_jrn HR) (conj (vepi_win HR) (conj (vepi_s0 HR) (conj (vepi_s2 HR)
  (conj (vepi_s10 HR) (conj (vepi_s8 HR) (conj (vepi_s5 HR) (conj (vepi_gp HR) (conj (vepi_tp HR) (conj (vepi_ra HR)
  (conj (vepi_saved HR) (conj (vepi_flag HR) (conj (vepi_frm HR) (conj (vepi_fregs HR) (vepi_rq HR)))))))))))))))).
Qed.

Local Unset Implicit Arguments.

(* ---- the callees ----
   fuzz_malloc (row 270) is the tree's published text PRH_FnAlloc.tfuzz_malloc_specX: a premise of the
   statement. __asan_memcpy (row 283) is the kit's intrinsic text WITH the memnorm keep (YGcallMxmn.v
   aintrin_realizes_xm at OCpy), which YGcallMxmn.aj_intrin_at_xm turns into the journal step: the Section hypothesis
   H_checked_memcpy_xm of lib/A/VrdNumTail.v, the one file whose proofs cross that call. *)

(* musl strtod (row 298, A 0x9aef0 = STRTOD). NOT a hypothesis any more: a Theorem Labs lane's row has landed
   (lib/Reusable/YStrtodRowX.v + lib/A/Prog/strtod_row.v, 94056d4f69e), and vrd_strtod_row below is
   strtod_row_aj_A at this slice's model and text predicate. The model is the frozen text's own
   PRH_Reader.prh_jr_strtod, read as the row's sm takes it, (bits, consumed); the bridge to the row's own
   strtod_model is strtod_model_scan_A (both are FloatScan.scan_strtod of the NUL-terminated token).
   The three image facts about B it needs are Section hypotheses here: an instance proves them of its own B. *)
Definition vrd_sm (txt : list Z) : option (Z * Z) := Some (snd (prh_jr_strtod txt), fst (prh_jr_strtod txt)).
Definition vrd_txt_ok (txt : list Z) : Prop :=
  Forall (fun c => numch c = true) txt /\ Z.of_nat (length txt) < 2 ^ 30.

Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis B_tp : as_tp B = STRTOD_TP.
Hypothesis B_errno : as_errno B = STRTOD_ERRNO.
Hypothesis B_errno_own : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).

(* the scan's byte set is inside musl's: PjGrammar.numch -> FmtFp_facts3.is_numch (RESTATEMENT of the released
   plain lib/Prog/PvNum.v:184 pvn_numch_is; both are pure byte tests) *)
Lemma vrd_numch_is : forall c, numch c = true -> FmtFp_facts3.is_numch c = true.
Proof.
  intros c H. unfold numch, digit in H. unfold FmtFp_facts3.is_numch.
  destruct (48 <=? c), (c <=? 57), (c =? 46), (c =? 101), (c =? 69), (c =? 43), (c =? 45); cbn in *; congruence.
Qed.

Lemma vrd_sm_of_model : forall txt bits c, strtod_model txt = Some (bits, c) -> vrd_sm txt = Some (bits, c).
Proof.
  intros txt bits c H. unfold vrd_sm, prh_jr_strtod. rewrite <- (strtod_model_scan_A txt), H. reflexivity.
Qed.

Lemma vrd_strtod_pc : pa_sigma AS_strtod = STRTOD.
Proof. vm_compute. reflexivity. Qed.

(* THE ROW at row 298, by name *)
Lemma vrd_strtod_row :
  aj_strtod_row (SK := SK) segs B ARx strtod_img_A prh_pst STRTOD STK_RT_STRTOD vrd_sm vrd_txt_ok.
Proof.
  apply (strtod_row_aj_A SK B prh_pst ARx LAWS B_tp B_errno B_errno_own STK_RT_STRTOD vrd_sm vrd_txt_ok).
  - unfold STK_RT_STRTOD, ESTACK, STRTOD_K. lia.
  - intros txt [HF HLen]. split; [|exact HLen].
    apply (Forall_impl _ vrd_numch_is HF).
  - intros txt bits c _ H. exact (vrd_sm_of_model txt bits c H).
Qed.

(* ---- the arm's RESULT, as the epilogue's RQ: the body of tparse_value_specX d's post with the return value
   rv in place of `getr regs' 10`, and no registers at all (the shared tail reloads them, so the arm cannot
   speak about the final ones; WalkAlive's epilogue step turns rv, which it reads out of s5, into the post's
   own register conjunct). RQ is read AT THE JOIN, where this call's fake frame (0, pos) is still live
   (vrd_disp_a: frames S = (0, pos) :: frames S0; the release is the tail's), so rd_blocks_move is spelled out
   with its frames clause at the join: frames S' is (0, pos) :: frames S0 up to order. The other three clauses
   are rd_blocks_move's verbatim. Every other conjunct is the text's own, VERBATIM and in the text's order, from
   the kit's CUT 7cdbb61b5fa0 (a working branch, PRH_FnParse.v blob f0d92dcec7e9, tparse_value_specX's post
   :314-384) with the entry state S read as S0: the ledger at the call's own `most own`, THE HULL USE
   (PresetHullBudget.hull_used from S0 over the all-granted events), the live-request Permutation
   (hlive_from), THE POSITION TRANSFER (quantified over any run and position the caller picks; no rp_* parameter and
   no agreement premise), THE OUTCOME clause over the ALL-GRANTED trace prhPv_gtrace, THE OUTCOME OF AN INJECTED
   READING (guarded: under the model's grant list PresetReqAt.okk with the chosen failure inside the value's window,
   every failed outcome the instance met is the chosen one, PRH_Base.prh_granted), the fixed rd_ledger_move (most
   and the granted trace), and in each arm of the result THE TREE'S FREE ORDER (FREEORD-NONE: pj_free's order list
   of the node against prhPv_frees, the first conjunct after the return value) and, in the Some arm, CAP's
   pj_ncapR after pj_nodeR. The position and the live set are read at the join; the release keeps both by conversion
   (PresetRoomPosKeep.room_pos_stack_free: stack_free_state moves only the fake frames). ---- *)
Definition vrd_pv_post (d : nat) (e q v text len p : Z) (tb : list Z)
  (ly0 : alayout) (S0 : astate) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (pos rv : Z)
  : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Prop :=
  fun ly' S' Hp' W' mem' =>
  exists (ok : list bool) res tr okr D Lam' peak' cnt' fail' ran',
    jr_value ReaderRes.jr_strtod d (rest_atR tb text p) ok = (res, tr, okr) /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\ room_live_cf S' /\
    (* the hull use: the allocator meters grew by at most the all-granted events' counts *)
    PresetHullBudget.hull_used S0 S' (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) /\
    Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
      (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) (PresetReqAt.rd_hevs tr)) /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
       (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
       PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S') /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
       (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
       PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
       PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) ->
       (fail < cnt \/ cnt + Z.of_nat (calls (prhPv_gtrace d (rest_atR tb text p))) <= fail) ->
       ran' = ran /\ fst (jr_value ReaderRes.jr_strtod d (rest_atR tb text p) []) = (res, tr) /\
       exists hist', PresetRoomPos.iface_room_pos sm x os
         (i + length (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))))%nat H0 hist' S') /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
       (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
       PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_value ReaderRes.jr_strtod d
         (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
       PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_value ReaderRes.jr_strtod d
         (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
       cnt <= fail < cnt + Z.of_nat (calls (prhPv_gtrace d (rest_atR tb text p))) ->
       PRH_Base.prh_granted ok cnt fail (calls tr)) /\
    rd_ledger_move Lam peak cnt fail ran most ok (prhPv_gtrace d (rest_atR tb text p)) tr D Lam' peak' cnt' fail'
      ran' /\
    (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly0 S0)) /\
    Permutation (ablocks B ly' S') (prhReader_ab D ++ ablocks B ly0 S0) /\
    Permutation (frames S') ((0, pos) :: frames S0) /\
    hpeakR tr <= 224 * Z.of_nat (length (rest_atR tb text p)) + 512 * Z.of_nat (PjGrammar.MAXD - d) /\
    blocks_bytes S' <= blocks_bytes S0 + prh_held tr /\
    Ledger.lsum D = PjGrammar.held tr /\
    match res with
    | Some (t, r) =>
        rv = 0 /\
        (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
           exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\
             map (fun b => snd b + cf_head) F = prhPv_frees d (rest_atR tb text p) ok) /\
        pj_in_okR segs (rdW W' mem') q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb /\
        pj_nodeR segs (rdW W' mem') (prh_lin Lam') v t D /\
        pj_ncapR segs (rdW W' mem') v t /\
        Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r))
    | None =>
        rv = -1 /\
        (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - d <= n)%nat ->
           exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\
             map (fun b => snd b + cf_head) F = prhPv_frees d (rest_atR tb text p) ok) /\
        pj_in_afterR segs (rdW W' mem') q text len (Z.of_nat d) 33 /\
        pj_fdR segs (rdW W' mem') (prh_lin Lam') (PjGrammar.MAXD - d) v D
    end.

(* ---- vrd_pv_post, NAMED. ADDITIVE: the definition above is unchanged. vrd_pv_R names each conjunct of its
   existential body in the definition's order, vrd_pv_RSome / vrd_pv_RNone the conjuncts of its two arms;
   vrd_pv_R_of reads vrd_pv_post into the records and vrd_pv_post_of_R builds it from them, so an arm proof that reads
   and builds the result through these is not broken by a conjunct appended later. ---- *)
Local Set Implicit Arguments.

Record vrd_pv_RSome (d : nat) (q v text len p : Z) (tb : list Z) (W' : world segs) (mem' : word -> option byte)
  (ok : list bool) (D Lam' : list (Z * Z)) (rv : Z) (t : PjTree.jv) (r : list Z) : Prop := {
  vpvs_rv : rv = 0;
  vpvs_freeord : cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
    exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\
      map (fun b => snd b + cf_head) F = prhPv_frees d (rest_atR tb text p) ok;
  vpvs_in_ok : pj_in_okR segs (rdW W' mem') q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb;
  vpvs_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam') v t D;
  vpvs_ncap : pj_ncapR segs (rdW W' mem') v t;
  vpvs_lsum_le : Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r)) }.

Record vrd_pv_RNone (d : nat) (q v text len p : Z) (tb : list Z) (W' : world segs) (mem' : word -> option byte)
  (ok : list bool) (D Lam' : list (Z * Z)) (rv : Z) : Prop := {
  vpvn_rv : rv = -1;
  vpvn_freeord : cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - d <= n)%nat ->
    exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\
      map (fun b => snd b + cf_head) F = prhPv_frees d (rest_atR tb text p) ok;
  vpvn_in_after : pj_in_afterR segs (rdW W' mem') q text len (Z.of_nat d) 33;
  vpvn_fd : pj_fdR segs (rdW W' mem') (prh_lin Lam') (PjGrammar.MAXD - d) v D }.

Record vrd_pv_R (d : nat) (e q v text len p : Z) (tb : list Z) (ly0 : alayout) (S0 : astate) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) (pos rv : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list Z)) (tr : list PjGrammar.ev)
  (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) : Prop := {
  vpv_run : jr_value ReaderRes.jr_strtod d (rest_atR tb text p) ok = (res, tr, okr);
  vpv_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own;
  vpv_room : room_live_cf S';
  vpv_hull : PresetHullBudget.hull_used S0 S' (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)));
  vpv_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) (PresetReqAt.rd_hevs tr));
  vpv_pos : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S';
  vpv_outcome : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
    PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) ->
    (fail < cnt \/ cnt + Z.of_nat (calls (prhPv_gtrace d (rest_atR tb text p))) <= fail) ->
    ran' = ran /\ fst (jr_value ReaderRes.jr_strtod d (rest_atR tb text p) []) = (res, tr) /\
    exists hist', PresetRoomPos.iface_room_pos sm x os
      (i + length (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))))%nat H0 hist' S';
  vpv_injected : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_value ReaderRes.jr_strtod d
      (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
    PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_value ReaderRes.jr_strtod d
      (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
    cnt <= fail < cnt + Z.of_nat (calls (prhPv_gtrace d (rest_atR tb text p))) ->
    PRH_Base.prh_granted ok cnt fail (calls tr);
  vpv_ledger_move : rd_ledger_move Lam peak cnt fail ran most ok (prhPv_gtrace d (rest_atR tb text p)) tr D Lam'
    peak' cnt' fail' ran';
  vpv_fresh : forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly0 S0);
  vpv_blocks : Permutation (ablocks B ly' S') (prhReader_ab D ++ ablocks B ly0 S0);
  vpv_frames : Permutation (frames S') ((0, pos) :: frames S0);
  vpv_hpeak : hpeakR tr <= 224 * Z.of_nat (length (rest_atR tb text p)) + 512 * Z.of_nat (PjGrammar.MAXD - d);
  vpv_bytes : blocks_bytes S' <= blocks_bytes S0 + prh_held tr;
  vpv_lsum : Ledger.lsum D = PjGrammar.held tr;
  vpv_arm : match res with
    | Some (t, r) => vrd_pv_RSome d q v text len p tb W' mem' ok D Lam' rv t r
    | None => vrd_pv_RNone d q v text len p tb W' mem' ok D Lam' rv
    end }.

Lemma vrd_pv_R_of : forall d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv ly' S' Hp' W' mem',
  vrd_pv_post d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv ly' S' Hp' W' mem' ->
  exists ok res tr okr D Lam' peak' cnt' fail' ran',
    vrd_pv_R d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv ly' S' Hp' W' mem' ok res tr okr D
      Lam' peak' cnt' fail' ran'.
Proof.
intros d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv ly' S' Hp' W' mem' H.
destruct H as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 &
  H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).
exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
refine {| vpv_run := H1; vpv_ledger := H2; vpv_room := H3; vpv_hull := H4; vpv_live := H5; vpv_pos := H6;
  vpv_outcome := H7; vpv_injected := H8; vpv_ledger_move := H9; vpv_fresh := H10; vpv_blocks := H11;
  vpv_frames := H12; vpv_hpeak := H13; vpv_bytes := H14; vpv_lsum := H15; vpv_arm := _ |}.
destruct res as [[t r]|].
- destruct H16 as (A1 & A2 & A3 & A4 & A5 & A6).
  exact {| vpvs_rv := A1; vpvs_freeord := A2; vpvs_in_ok := A3; vpvs_node := A4; vpvs_ncap := A5;
           vpvs_lsum_le := A6 |}.
- destruct H16 as (A1 & A2 & A3 & A4).
  exact {| vpvn_rv := A1; vpvn_freeord := A2; vpvn_in_after := A3; vpvn_fd := A4 |}.
Qed.

Lemma vrd_pv_post_of_R : forall d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv ly' S' Hp' W' mem'
    ok res tr okr D Lam' peak' cnt' fail' ran',
  vrd_pv_R d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv ly' S' Hp' W' mem' ok res tr okr D
    Lam' peak' cnt' fail' ran' ->
  vrd_pv_post d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv ly' S' Hp' W' mem'.
Proof.
intros d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv ly' S' Hp' W' mem' ok res tr okr D Lam'
  peak' cnt' fail' ran' HR.
exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
refine (conj (vpv_run HR) (conj (vpv_ledger HR) (conj (vpv_room HR) (conj (vpv_hull HR) (conj (vpv_live HR)
  (conj (vpv_pos HR) (conj (vpv_outcome HR) (conj (vpv_injected HR) (conj (vpv_ledger_move HR) (conj (vpv_fresh HR)
  (conj (vpv_blocks HR) (conj (vpv_frames HR) (conj (vpv_hpeak HR) (conj (vpv_bytes HR) (conj (vpv_lsum HR)
  _))))))))))))))).
pose proof (vpv_arm HR) as HA. clear HR. destruct res as [[t r]|].
- exact (conj (vpvs_rv HA) (conj (vpvs_freeord HA) (conj (vpvs_in_ok HA) (conj (vpvs_node HA)
    (conj (vpvs_ncap HA) (vpvs_lsum_le HA)))))).
- exact (conj (vpvn_rv HA) (conj (vpvn_freeord HA) (conj (vpvn_in_after HA) (vpvn_fd HA)))).
Qed.

Local Unset Implicit Arguments.

(* ---- the segment lemma's statement ----
   From the dispatch state with the number arm selected (VrdPro.vrd_disp_a at VA_num, whose pc is
   pa_sigma AS_parse_value + 0x26c = PV_NUM), the arm runs to the SHARED JOIN at row 225 and leaves the state
   vrd_epi_a with its own result as RQ. The epilogue step from there to tparse_value_specX d's post is lane
   WalkAlive's (lib/A/VrdEpi.v); this lane owns rows 157..224 and the definition of vrd_epi_a. The premises
   besides vrd_disp_a are the call's own, VERBATIM from tparse_value_specX (the kit's cut, PRH_FnParse.v blob f0d92dcec7e9):
   fpre, the argument registers and rd_pre at the call's `most own`; and fuzz_malloc's published text. There is NO
   entry position: the text has none (its position is the post's transfer, which the arm proves at whatever run and
   position the caller picks). The text's position-free LIVE COUNTS (:251-254, which give the row-270 malloc its
   sec_cnt / ccnt24 premises) are vrd_disp_body's (VrdPro.v, one home), so this statement carries no copy of them;
   the instance fact cf_head = PresetReqAt.HEAD is the Section hypothesis HI_head of the files whose proofs use it
   (VrdNumTail.v, VrdNumA.v). The flag word at F + 56 is vrd_frame's (VrdPro.v b50e4aac4a2), so no premise of this
   statement stands in for it. THE HULL BUDGET, the text's entry premise `hull_budget S0 (rd_hevs (prhPv_gtrace d ..))`
   (lib/Spec/PresetHullBudget.v), comes right after vrd_disp_a: the arm pays the row-270 malloc's one-event budget from
   it (the granted trace is that one allocation), and the post's hull use is that call's. *)
Definition vrd_num_a_stmt : Prop :=
  forall (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
         (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)) (CTX0 : list (list Z)) (CW : list (list Z))
         (e q v text len p : Z) (d : nat) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
         (W : world segs) (c : config),
  tfuzz_malloc_specX B ARx SK ->
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  getr regs0 10 = w64 q -> getr regs0 11 = w64 v ->
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    W c ->
  PresetHullBudget.hull_budget S0 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
  match PjGrammar.skip (rest_atR tb text p) with b :: _ => vrd_arm_of b = VA_num | [] => False end ->
  SRr segs W c
    (fun W' c' => exists (fx2 : YK11.FPState) (pos rv : Z),
       vrd_epi_a fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
         (vrd_pv_post d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv)
         W' c').

(* ---- the same statement with the GENERIC MEMORY INVARIANT P (a Theorem Labs lane's 12:19Z ruling). WHY P IS IN THE
   STATEMENT: an SRr post is opaque once Qed, so an end-state memory invariant must be in the segment's STATEMENT;
   the generic SRr_memnorm was measured NOT provable (a Theorem Labs lane), so it cannot be added afterwards. P comes with its
   laws srr_inv_laws (the runs), the call law srr_inv_call (fuzz_malloc's, __asan_memcpy's and strtod's posts carry
   the memnorm keep) and the entry law srr_inv_mn (strtod's row takes memnorm at entry); P holds of the memory at the
   dispatch and the arm concludes P of the memory at the join. Its instance (the unit's top) is the memnorm keep from
   parse_value's entry memory, P := fun m => memnorm segs mem0 -> memnorm segs m, with YSRrMemnorm.srr_inv_laws_imp
   over srr_inv_laws_memnorm_k, srr_inv_call_imp, and srr_inv_mn_imp from tparse_value_specX's own memnorm premise
   at mem0. vrd_num_a_stmt's premises and conclusion are vrd_num_a_stmt_at's, verbatim, with P of the memory at the
   dispatch added last and P of the memory at the join added to the conclusion; vrd_num_a_stmt_P closes it over every
   P with the three laws (unfolded, it is `forall P, srr_inv_laws segs P -> srr_inv_call segs P -> srr_inv_mn segs P ->
   <vrd_num_a_stmt's premises> -> P (ms_mem (cfg_ms c)) -> SRr segs W c (fun W' c' => (exists fx2 pos rv, vrd_epi_a ..
   (vrd_pv_post ..) W' c') /\ P (ms_mem (cfg_ms c')))`). ---- *)
Definition vrd_num_a_stmt_at (P : (word -> option byte) -> Prop) : Prop :=
  forall (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
         (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)) (CTX0 : list (list Z)) (CW : list (list Z))
         (e q v text len p : Z) (d : nat) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
         (W : world segs) (c : config),
  tfuzz_malloc_specX B ARx SK ->
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  getr regs0 10 = w64 q -> getr regs0 11 = w64 v ->
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    W c ->
  PresetHullBudget.hull_budget S0 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
  match PjGrammar.skip (rest_atR tb text p) with b :: _ => vrd_arm_of b = VA_num | [] => False end ->
  P (ms_mem (cfg_ms c)) ->
  SRr segs W c
    (fun W' c' => (exists (fx2 : YK11.FPState) (pos rv : Z),
       vrd_epi_a fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
         (vrd_pv_post d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv)
         W' c') /\ P (ms_mem (cfg_ms c'))).
Definition vrd_num_a_stmt_P : Prop :=
  forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P -> srr_inv_call segs P -> srr_inv_mn segs P ->
  vrd_num_a_stmt_at P.

(* ================================================================================================================
   THE WALK. Every state is rebuilt from the CURRENT registers (E = Eimg (Ereg regs extras)), so every symbolic
   value is an atom of a register and no term grows across a run. ROW n is listing slot n + 4682 of
   lib/A/Listing_prog.v, i.e. byte offset 4 * (n + 4682) from the listing's base; row 2 is parse_value's entry.
   ================================================================================================================ *)
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

Definition vrd_row (n : nat) : Z := 4 * Z.of_nat (n + 4682).
Definition vrd_E (regs : bvmap 5 word) : env := @Eimg _ A_prog_listing PI_prog_A (Ereg regs []).

(* The rows that write the frame's OWN shadow band (row 157 and row 327) cannot run with the real shadow base:
   cells_safe_b refuses a writable window that meets Bspan unless an SH entry covers it, and that entry would be
   the shadow of the shadow. They run with no shadow checks at all (Bx = 0, Bspan = (0, 0), SH = []), which is
   sound because they resolve no ASan check. *)
Definition vrd_Bx0 : sv := SLit 0.
Definition vrd_Bspan0 : Z * Z := (0, 0).

(* ---- THE REFUSAL JOIN, rows 326..328 (A 0x86420..0x86428): `addi a0, zero, -8`, `sb a0, 4(s8)` (the endptr
   local's granule poisoned again) and `j` to the shared epilogue at row 225. Five refusals reach it with s5
   already -1: the bound test of row 162, the first-byte digit test of row 170, the leading-zero test of row 182,
   the NULL block of row 277 and the two strtod tests of rows 311 and 315. ---- *)
Definition vrd_ref_a (d : nat) (e q v : Z)
  (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (pos rv : Z)
  (RQ : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Prop)
  : world segs -> config -> Prop :=
  fun W c => exists (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ly : alayout) (S : astate)
                    (Hp : list Z) (k : Z),
  c = cfg_at segs (pa_sigma AS_parse_value + PV_REF) regs mem md /\
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k /\
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W) mem a = aview segs (w_H W0) mem0 a) /\
  getr regs 8 = w64 (spZ regs0) /\
  getr regs 18 = w64 (frame_addr ly 0 pos) /\ getr regs 26 = w64 (frame_addr ly 0 pos) /\
  getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) /\ getr regs 21 = w64 rv /\
  getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\ YK0s.ret_ok (getr regs0 1) /\
  vrd_saved (rdW W mem) (spZ regs0) regs0 /\
  val_mem segs (rdW W mem) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) /\
  In (0, pos) (frames S) /\ frm_zero (@YK11.fp_csr fx) /\ 0 <= e /\
  RQ ly S Hp W mem.

(* the frame of the eight shadow bytes of this call's own frame: the only bytes rows 326..328 write. Everything a
   reader result speaks of - the node, the cursor, the text, the statics, the block heads - is in the application
   (in_app) or in the image, and the shadow band meets neither, so vrd_pv_post satisfies it (vrd_pv_post_sh_frame).
   The state's allocator relation is given (the blocks' places come from its blocks law), and presence is the
   restricted memory's growth (writability moves with it). *)
Definition vrd_sh_frame
  (RQ : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Prop) : Prop :=
  forall ly' S' Hp' (Wx : world segs) (m m' : word -> option byte) (md : Model),
  ARx ly' S' Hp' Wx m md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < kHighShadowEnd) ->
     aview segs (w_H Wx) m' a = aview segs (w_H Wx) m a) ->
  mem_grows (rdW Wx m) (rdW Wx m') ->
  RQ ly' S' Hp' Wx m -> RQ ly' S' Hp' Wx m'.

Definition vrd_ref_regions : smem := [ YP09.mkRegion (Some 24%nat) 4 5 4 5 [] ].
Definition vrd_ref_facts : facts := mkFacts [ (24%nat, mkAF 4096 (2 ^ 46) 0) ] [] [].
Definition ss_vrd_ref : sstate := mkSS (vrd_row 326) sr_atoms vrd_ref_regions None vrd_ref_facts.

Lemma vrd_pc_ref : pa_sigma AS_parse_value + PV_REF = BASE + vrd_row 326.
Proof. vm_compute. reflexivity. Qed.
Lemma vrd_pc_epi : pa_sigma AS_parse_value + PV_EPI = BASE + vrd_row 225.
Proof. vm_compute. reflexivity. Qed.

(* the recursion's stack bound is a length: the kit's PrhImg field pi_frame_nonneg (PRH_Base.v:143) *)
Lemma vrd_stk_nonneg : forall d, 0 <= STK_parse_value d.
Proof.
intros d. unfold STK_parse_value, LEAF_pv_pi, zmaxl. cbn [fold_right].
assert (H0 : 0 <= pi_frame F_parse_value + pi_frame F_parse_items).
{ pose proof (pi_frame_nonneg F_parse_value). pose proof (pi_frame_nonneg F_parse_items). lia. }
pose proof (Z.mul_nonneg_nonneg _ _ (Nat2Z.is_nonneg (S (PjGrammar.MAXD - d))) H0) as H3.
lia.
Qed.

(* the one symbolic state the refusal join needs: the frame's shadow granule 4, writable *)
Lemma vrd_st_ref : forall (W : world segs) regs mem base,
  bv_unsigned (getr regs 24) = base -> 4096 <= base /\ base + 5 <= 2 ^ 46 ->
  writable_at segs (rdW W mem) (base + 4) ->
  st_ok_pi segs VAL (vrd_E regs) ss_vrd_ref
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 326)) mem (seg_rom segs))).
Proof.
intros W regs mem base Hb Hr Hw. rewrite restrict_mkst_fx.
assert (E24 : ew (vrd_E regs) 24 = getr regs 24)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
unfold ss_vrd_ref. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold vrd_ref_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E24, Hb. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. replace o with 4 by lia. exact Hw.
- apply pairwise_disjoint_of_extents. unfold vrd_ref_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [vrd_ref_facts f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E24, Hb.
  rewrite Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
Qed.

(* rows 326..328: the state at the join, with the arm's own result carried through the one shadow byte they write. The
   number arm stores no wild trace, so its journal is at the empty budget, which every CW's wbudget CW 0 admits *)
Lemma vrd_ref_join : forall d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c,
  vrd_sh_frame RQ ->
  vrd_ref_a d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c ->
  SRr segs W c (vrd_epi_a fx d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ).
Proof.
intros d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c HRQfr
  (regs & mem & md & ly & S & Hp & k & -> & HJ & HWIN & R8 & R18 & R26 & R24 & R21 & R3 & R4 & Hra & HSAV & HFLAG
   & HinF & HFZ & HE0 & HRQ0).
pose proof (vrd_stk_nonneg d) as HSTK.
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTACK & _).
pose proof HSTACK as (_ & _ & Hclo & Hlo & Hhi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (HF0 & HFc & HFapp).
destruct (alx_frames segs B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (_ & _ & _ & HFsh).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
rewrite Hfb in HFc, HFsh.
assert (HD8 : 0 <= frame_addr ly 0 pos / 8 <= alloc_ceiling / 8).
{ split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]. }
assert (HAC8 : alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
assert (Hb24 : bv_unsigned (getr regs 24) = SHADOW_OFF + frame_addr ly 0 pos / 8)
  by (rewrite R24; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (Hi4 : 0 <= 4 < 64 / 8) by (replace (64 / 8) with 8 by reflexivity; lia).
assert (Hw24 : writable_at segs (rdW W mem) (SHADOW_OFF + frame_addr ly 0 pos / 8 + 4)).
{ apply (apresent_writable segs). replace (SHADOW_OFF + frame_addr ly 0 pos / 8 + 4)
    with (shadow_addr (frame_addr ly 0 pos) + 4) by (unfold shadow_addr; lia).
  exact (proj1 (HFsh 4 Hi4)). }
pose proof (vrd_st_ref W regs mem _ Hb24 ltac:(unfold SHADOW_OFF in *; lia) Hw24) as HS.
unfold cfg_at. rewrite vrd_pc_ref.
assert (E24 : ew (vrd_E regs) 24 = getr regs 24)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
assert (HEI : img_env VAL A_LIM (vrd_E regs)) by (unfold vrd_E; apply Eimg_env).
assert (SHOK : sh_ok segs vrd_Bx0 (@nil shent) (vrd_E regs) (rdW W mem)) by (apply Forall_nil).
pose (RUNTO := paj_run_to_x (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS).
paj_run_to_tok_x RUNTO HS HJ SHOK vrd_Bspan0 (vrd_row 225).
- (* the write premise: the only window is the frame's own shadow granule *)
  intros a Ha. destruct Ha as (r & Hin & Hr). cbn [vrd_ref_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite E24, Hb24 in Hr.
  right; right; right. exists 0, pos. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Hfb. lia.
- (* the state at the join *)
  pmkst HS.
  prreg HS (8%bv : bv 5) P8. prreg HS (18%bv : bv 5) P18. prreg HS (26%bv : bv 5) P26.
  prreg HS (24%bv : bv 5) P24. prreg HS (21%bv : bv 5) P21. prreg HS (3%bv : bv 5) P3.
  prreg HS (4%bv : bv 5) P4.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
    assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < kHighShadowEnd) ->
              aview segs (w_H W) mT a = aview segs (w_H W) mem a)
  end.
  { intros a Ha64 Ha. unfold aview. f_equal. unfold mbyte.
    rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). cbn [vrd_ref_regions In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E24, Hb24 in Hr.
    rewrite unsigned_lit_small in Hr by exact Ha64.
    apply Ha. unfold kHighShadowEnd, SHADOW_OFF in *. lia. }
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  assert (HKLS : kLowShadowBeg = 2147446784) by reflexivity.
  assert (KV : forall a (n : nat) vv, val_mem segs (rdW W mem) a n vv ->
     spZ regs0 - 104 <= a -> a + Z.of_nat n <= spZ regs0 -> val_mem segs (rdW W (ms_mem ms)) a n vv).
  { intros a n vv Hv Ha1 Ha2. eapply val_mem_kept; [|exact Hv]. intros kk Hk.
    apply HKEEP; lia. }
  assert (HFband : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 ->
     0 <= a < 2 ^ 64 /\ ~ (SHADOW_OFF <= a < kHighShadowEnd)).
  { unfold in_app, ASAN_CEIL in HFapp. rewrite Hfb in HFapp.
    destruct HFapp as (HF4096 & [Hlow | [Hhigh1 Hhigh2]]); intros a Ha; split; lia. }
  apply SRr_ret.
  exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md), ly, S, Hp, k.
  split; [rewrite vrd_pc_epi; reflexivity|].
  (* the empty budget: ajournal_x is ajournal_xw at [] (YCbqG.v), and wbudget CW 0 [] is 0 <= 0 by computation *)
  split; [exists []; split; [exact HJ | exact (le_n 0)]|].
  split.
  { intros a Ha Hn. rewrite HKEEP by (unfold kHighShadowEnd, SHADOW_OFF in *; lia).
    exact (HWIN a Ha Hn). }
  split; [rewrite P8; exact R8|].
  split; [rewrite P18; exact R18|].
  split; [rewrite P26; exact R26|].
  split; [rewrite P24; exact R24|].
  split; [rewrite P21; exact R21|].
  split; [rewrite P3; exact R3|].
  split; [rewrite P4; exact R4|].
  split; [exact Hra|].
  split.
  { unfold vrd_saved in HSAV |- *.
    destruct HSAV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
    repeat split; (eapply KV; [eassumption | cbn; lia | cbn; lia]). }
  split.
  { eapply val_mem_kept; [|exact HFLAG]. intros kk Hk.
    destruct (HFband (frame_addr ly 0 pos + 56 + kk) ltac:(lia)) as [Hr1 Hr2].
    apply HKEEP; [exact Hr1 | exact Hr2]. }
  split; [exact HFZ|].
  split; [intros rr; reflexivity|].
  exact (HRQfr ly S Hp W mem (ms_mem ms) md HAR HKEEP HG HRQ0).
Qed.

(* ---- the arm's result survives a write confined to the shadow band (vrd_sh_frame): the five statics are image
   bytes (H_pst_img, an image fact: lib/A/Prog/S1ImgA.v pst_in_img_A at prh_img_A), every harness block of the ledger
   (heads and user bytes; the subtree's blocks D are among them) is an application block by the state's blocks law,
   and the cursor, the node and the text lie outside the band (the dispatch's own facts about q, v, text). ---- *)
Lemma vrd_pv_post_sh_frame : forall d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv,
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  kHighShadowEnd <= q -> q + 24 <= 2 ^ 64 ->
  0 <= v -> amem_range v 56 -> amem_range text len ->
  vrd_sh_frame (vrd_pv_post d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv).
Proof.
intros d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv
  H_pst_img Hq1 Hq2 Hv0 Hamv Hamt ly' S' Hp' Wx m m' md HAR HKP HMG HRQ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HKLS : kLowShadowBeg = 2147446784) by reflexivity.
pose proof cf_head_nonneg as Hch.
unfold vrd_pv_post in HRQ |- *.
destruct HRQ as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HJV & HLED & HRL & HHU & HLV & HRP &
  HOC & HINJ & HLM & HDF & HAB & HFR & HHP & HBB & HLS & HM).
(* a harness block's bytes, its head included, are application bytes *)
assert (BLK : forall a k x, In (a, k) Lam' -> a - cf_head <= x < a + k \/ a - cf_head <= x < a - cf_head + 8 ->
          aview segs (w_H Wx) m' x = aview segs (w_H Wx) m x).
{ intros a k x Hin Hx.
  pose proof HLED as (_ & _ & HFA & _). rewrite Forall_forall in HFA.
  destruct (HFA (a, k) Hin) as (Hk0 & Hab & _ & _ & _). cbn [fst snd] in Hk0, Hab.
  destruct (alx_blocks segs B ARx LAWS ly' S' Hp' Wx m md _ _ HAR Hab) as (_ & Hb4 & Hbc & Hbapp & _).
  assert (Hn0 : 0 <= k + cf_head) by lia.
  pose proof (req_size_pos (k + cf_head) Hn0) as Hrq.
  unfold in_app, ASAN_CEIL in Hbapp. apply HKP; lia. }
assert (DL : forall b, In b D -> In b Lam').
{ intros b Hb. destruct HLM as (_ & _ & _ & HPL & _).
  apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hb. }
assert (AGR : pj_agreeR segs (rdW Wx m) (rdW Wx m') (pj_footR v D)).
{ intros x Hx. split.
  - apply (mbyte_of_aview segs). destruct Hx as [Hx | ((a, k) & Hb & Hx)].
    + apply HKP; unfold amem_range in Hamv; lia.
    + unfold pj_holdsR in Hx. cbn [fst snd] in Hx. apply (BLK a k x); [exact (DL _ Hb) | left; lia].
  - intros Hw. exact (writable_at_grows segs _ _ x HMG Hw). }
exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
split; [exact HJV|].
split.
{ apply (S1Ledger.prh_ledger_kept_aview B ly' S' Hp' Wx m ly' S' Hp' Wx m' Lam' peak' cnt' fail' ran' most own HLED).
  - intros a Ha. pose proof (@pa_segs_low _ A_prog_listing PI_prog_A a (H_pst_img a Ha)) as Hlo'. apply HKP; lia.
  - intros a k i Hin Hi. apply (BLK a k); [exact Hin | right; lia].
  - intros a k _ H. exact H.
  - apply Permutation_refl. }
split; [exact HRL|]. split; [exact HHU|]. split; [exact HLV|]. split; [exact HRP|]. split; [exact HOC|].
split; [exact HINJ|]. split; [exact HLM|].
split; [exact HDF|]. split; [exact HAB|].
split; [exact HFR|]. split; [exact HHP|]. split; [exact HBB|]. split; [exact HLS|].
(* the tree's free order (the cut's FREEORD-NONE conjunct) by PRH_PjOrder.pj_foR_frame: its blocks are the
   subtree's, all in Lam' *)
assert (FO : forall n F, PRH_PjOrder.pj_foR segs (rdW Wx m) (prh_lin Lam') n v D F ->
  PRH_PjOrder.pj_foR segs (rdW Wx m') (prh_lin Lam') n v D F).
{ intros n F HF. apply (PRH_PjOrder.pj_foR_frame segs n _ _ (prh_lin Lam') (prh_lin Lam') v D F HF); [|exact AGR].
  intros a k Hin. exact (DL (a, k) Hin). }
destruct res as [[t r]|].
- destruct HM as (Hrv & HFO & HIN & HND & HNC & HLD).
  split; [exact Hrv|].
  split; [intros HH n Hn; destruct (HFO HH n Hn) as (F & HF1 & HF2); exists F; split; [exact (FO n F HF1) | exact HF2]|].
  split; [|split; [exact (pj_nodeR_frame segs t _ _ _ v D HND AGR) |
                   split; [exact (vrd_ncapR_frame segs t _ _ _ v D HND HNC AGR) | exact HLD]]].
  destruct HIN as (Vq & Vq8 & Vq16 & Hrw & Hq8 & Ht0 & Htl & Hpr & Hlen & GT & Hdj & Hd).
  split; [eapply val_mem_kept; [|exact Vq]; intros kk Hk; cbn in Hk; apply HKP; lia|].
  split; [eapply val_mem_kept; [|exact Vq8]; intros kk Hk; cbn in Hk; apply HKP; lia|].
  split; [eapply val_mem_kept; [|exact Vq16]; intros kk Hk; cbn in Hk; apply HKP; lia|].
  split; [intros x Hx; exact (writable_at_grows segs _ _ x HMG (Hrw x Hx))|].
  split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hpr|]. split; [exact Hlen|].
  split; [|split; [exact Hdj | exact Hd]].
  apply (garr8R_frame segs _ _ text tb GT). intros x Hx. apply (mbyte_of_aview segs).
  apply HKP; unfold amem_range in Hamt; lia.
- destruct HM as (Hrv & HFO & HAF & HFD).
  split; [exact Hrv|].
  split; [intros HH n Hn; destruct (HFO HH n Hn) as (F & HF1 & HF2); exists F; split; [exact (FO n F HF1) | exact HF2]|].
  split; [|exact (vrd_fdR_frame segs _ _ _ _ _ _ HFD AGR)].
  destruct HAF as (p0 & d0 & Hp0 & Hd0 & Vq & Vq8 & Vq16 & Hrw).
  exists p0, d0. split; [exact Hp0|]. split; [exact Hd0|].
  split; [eapply val_mem_kept; [|exact Vq]; intros kk Hk; cbn in Hk; apply HKP; lia|].
  split; [eapply val_mem_kept; [|exact Vq8]; intros kk Hk; cbn in Hk; apply HKP; lia|].
  split; [eapply val_mem_kept; [|exact Vq16]; intros kk Hk; cbn in Hk; apply HKP; lia|].
  intros x Hx. exact (writable_at_grows segs _ _ x HMG (Hrw x Hx)).
Qed.

(* ---- SEGMENT SA, rows 157..162 (A 0x8617c..0x86190): `sb zero, 4(s8)` unpoisons the endptr local's granule,
   `addi a1, a1, -0x2d` / `seqz a3, a1` / `add s6, a0, a3` set s6 = p' + j with j = (b = '-'), `addi s5, zero, -1`
   presets the return value, and `bgeu s6, a2` refuses when nothing is left after the sign. The ONE branch is
   decided by the model's own skipn: with j = 0 it cannot be taken (the dispatch gives p' < text + len), so the
   refusal arm is exactly the model's `skipn (vrd_j b) (b :: y) = []`.
   The run has no ASan check of its own (the shadow byte it writes is the frame's, so the shadow base is inert,
   vrd_Bx0 / vrd_Bspan0 / SH = []), and `seqz` is pinned by hand: the engine cannot fold it for b < 45 because
   b - 45 wraps, and the pin is the model's vrd_j. ---- *)
Definition vrd_sa_regions : smem := [ YP09.mkRegion (Some 24%nat) 4 5 4 5 [] ].
Definition vrd_sa_facts : facts := mkFacts [ (24%nat, mkAF 4096 (2 ^ 46) 0) ] [] [].
Definition ss_vrd_sa : sstate := mkSS (vrd_row 157) sr_atoms vrd_sa_regions None vrd_sa_facts.

Lemma vrd_pc_num : pa_sigma AS_parse_value + PV_NUM = BASE + vrd_row 157.
Proof. vm_compute. reflexivity. Qed.

Lemma vrd_st_sa : forall (W : world segs) regs mem base (n : nat),
  bv_unsigned (getr regs 24) = base -> 4096 <= base /\ base + 5 <= 2 ^ 46 ->
  writable_at segs (rdW W mem) (base + 4) ->
  st_ok_pi segs VAL (vrd_E regs) (mkSS (vrd_row n) sr_atoms vrd_sa_regions None vrd_sa_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row n)) mem (seg_rom segs))).
Proof.
intros W regs mem base n Hb Hr Hw. rewrite restrict_mkst_fx.
assert (E24 : ew (vrd_E regs) 24 = getr regs 24)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold vrd_sa_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E24, Hb. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. replace o with 4 by lia. exact Hw.
- apply pairwise_disjoint_of_extents. unfold vrd_sa_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [vrd_sa_facts f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E24, Hb.
  rewrite Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
Qed.

(* the registers rows 157..162 leave alone, as the later segments read them *)
Definition vrd_kept_regs (regs' regs : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 10 = getr regs 10 /\
  getr regs' 12 = getr regs 12 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\
  getr regs' 20 = getr regs 20 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\
  getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

(* presence across a segment: the restricted memory only grows (each run's mem_grows, chained) *)
Lemma vrd_mg_trans : forall m1 m2 m3 : word -> option byte, mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. exact (H23 x (H12 x Hx)). Qed.

(* the generic-invariant twin (P with srr_inv_laws; YC1fPx's paj_run_x_inv / paj_run_to_x_inv): P of the entry memory
   and P of each exit's memory *)
Lemma vrd_seg_sa_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (b p' text len : Z) (Q : world segs -> config -> Prop),
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  P mem ->
  In (0, pos) (frames S) ->
  getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
  getr regs 10 = w64 p' -> getr regs 11 = w64 b -> getr regs 12 = w64 (text + len) ->
  0 <= b < 256 -> 4096 <= text -> text <= p' <= text + len -> text + len < 2 ^ 62 ->
  (* the refusal arm (row 162 taken): nothing is left after the sign *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' -> P mem' ->
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (SHADOW_OFF + frame_addr ly 0 pos / 8 <= a < SHADOW_OFF + frame_addr ly 0 pos / 8 + 8) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     vrd_kept_regs regs' regs ->
     getr regs' 21 = w64 (-1) -> getr regs' 22 = w64 (p' + Z.of_nat (vrd_j b)) ->
     getr regs' 13 = w64 (Z.of_nat (vrd_j b)) ->
     text + len <= p' + Z.of_nat (vrd_j b) ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  (* the fall-through at row 163: the first token byte is at s6 = p' + j *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' -> P mem' ->
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (SHADOW_OFF + frame_addr ly 0 pos / 8 <= a < SHADOW_OFF + frame_addr ly 0 pos / 8 + 8) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     vrd_kept_regs regs' regs ->
     getr regs' 21 = w64 (-1) -> getr regs' 22 = w64 (p' + Z.of_nat (vrd_j b)) ->
     getr regs' 13 = w64 (Z.of_nat (vrd_j b)) ->
     p' + Z.of_nat (vrd_j b) < text + len ->
     SRr segs W (cfg_at segs (BASE + vrd_row 163) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 157) regs mem md) Q.
Proof.
intros P PLAW d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md b p' text len Q
  HJ HPM HinF R24 R10 R11 R12 Hb Htext Hp'r Hlen HREF HNXT.
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (HF0 & HFc & HFapp).
destruct (alx_frames segs B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (_ & _ & _ & HFsh).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
rewrite Hfb in HFc, HFsh.
assert (HD8 : 0 <= frame_addr ly 0 pos / 8 <= alloc_ceiling / 8).
{ split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]. }
assert (HAC8 : alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (Hb24 : bv_unsigned (getr regs 24) = SHADOW_OFF + frame_addr ly 0 pos / 8)
  by (rewrite R24; apply unsigned_lit_small; lia).
assert (Hi4 : 0 <= 4 < 64 / 8) by (replace (64 / 8) with 8 by reflexivity; lia).
assert (Hw24 : writable_at segs (rdW W mem) (SHADOW_OFF + frame_addr ly 0 pos / 8 + 4)).
{ apply (apresent_writable segs). replace (SHADOW_OFF + frame_addr ly 0 pos / 8 + 4)
    with (shadow_addr (frame_addr ly 0 pos) + 4) by (unfold shadow_addr; lia).
  exact (proj1 (HFsh 4 Hi4)). }
pose proof (vrd_st_sa W regs mem _ 157 Hb24 ltac:(lia) Hw24) as HS.
assert (E24 : ew (vrd_E regs) 24 = getr regs 24)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
assert (HEI : img_env VAL A_LIM (vrd_E regs)) by (unfold vrd_E; apply Eimg_env).
assert (SHOK : sh_ok segs vrd_Bx0 (@nil shent) (vrd_E regs) (rdW W mem)) by (apply Forall_nil).
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
unfold cfg_at.
paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan0.
- intros a Ha. destruct Ha as (r & Hin & Hr). cbn [vrd_sa_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite E24, Hb24 in Hr.
  right; right; right. exists 0, pos. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Hfb. lia.
- lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ =>
    assert (HKEEP : forall a, 0 <= a < 2 ^ 64 ->
              ~ (SHADOW_OFF + frame_addr ly 0 pos / 8 <= a < SHADOW_OFF + frame_addr ly 0 pos / 8 + 8) ->
              aview segs (w_H W) (ms_mem msq) a = aview segs (w_H W) mem a)
  end.
  { intros a Ha64 Ha. unfold aview. f_equal. unfold mbyte.
    rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). cbn [vrd_sa_regions In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E24, Hb24 in Hr.
    rewrite unsigned_lit_small in Hr by exact Ha64.
    apply Ha. lia. }
  assert (HGR : mem_grows (rdW W mem) (rdW W (ms_mem ms))) by exact HG.
  assert (E10 : bv_unsigned (ew (vrd_E regs) 10) = p').
  { unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10. apply unsigned_lit_small. lia. }
  assert (E11 : bv_unsigned (ew (vrd_E regs) 11) = b).
  { unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), R11. apply unsigned_lit_small. lia. }
  assert (E12 : bv_unsigned (ew (vrd_E regs) 12) = text + len).
  { unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), R12. apply unsigned_lit_small. lia. }
  assert (Hjr : 0 <= Z.of_nat (vrd_j b) <= 1) by (unfold vrd_j; destruct (b =? 45); cbn; lia).
  assert (HUj : YP0e.U (vrd_E regs) (SAlu ALU_SLTU (SOff 11 (-45)) (SLit 1)) = Z.of_nat (vrd_j b)).
  { rewrite YP0e.U_SAlu, YP0e.U_SOff, YP0e.U_SLit, E11. cbn [zalu_raw].
    rewrite (YP0m.zcanon_small 1) by lia. unfold vrd_j.
    destruct (Z.eqb_spec b 45) as [->|Hne].
    - replace (45 + -45) with 0 by lia. rewrite (YP0m.zcanon_small 0) by lia.
      cbn [Z.of_nat]. apply YP0m.zcanon_small. cbn. lia.
    - replace (zcanon (b + -45) <? 1) with false
        by (symmetry; apply Z.ltb_ge; exact (vrd_sub45_ge1 b ltac:(lia) Hne)).
      cbn [Z.of_nat]. apply YP0m.zcanon_small. cbn. lia. }
  assert (HUs : YP0e.U (vrd_E regs) (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SOff 11 (-45)) (SLit 1)))
                = p' + Z.of_nat (vrd_j b)).
  { rewrite YP0e.U_SAlu, YP0e.U_SOff, HUj, E10, Z.add_0_r. cbn [zalu_raw].
    rewrite (YP0m.zcanon_small p') by lia. apply YP0m.zcanon_small. lia. }
  assert (HUe : YP0e.U (vrd_E regs) (SOff 12 0) = text + len)
    by (rewrite YP0e.U_SOff, E12, Z.add_0_r; apply YP0m.zcanon_small; lia).
  pose proof HUs as HUs'. pose proof HUe as HUe'. unfold YP0e.U in HUs', HUe'.
  pose proof HUs as HU22. unfold YP0e.U in HU22.
  cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in HU22.
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in HU22.
  pose proof HUj as HU13. unfold YP0e.U in HU13.
  cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in HU13.
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in HU13.
  assert (EQ2 : ew (vrd_E regs) 2 = getr regs 2) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (EQ3 : ew (vrd_E regs) 3 = getr regs 3) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
  assert (EQ4 : ew (vrd_E regs) 4 = getr regs 4) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
  assert (EQ8 : ew (vrd_E regs) 8 = getr regs 8) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
  assert (EQ9 : ew (vrd_E regs) 9 = getr regs 9) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (EQ10 : ew (vrd_E regs) 10 = getr regs 10) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
  assert (EQ12 : ew (vrd_E regs) 12 = getr regs 12) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 12 12%bv eq_refl)).
  assert (EQ18 : ew (vrd_E regs) 18 = getr regs 18) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
  assert (EQ19 : ew (vrd_E regs) 19 = getr regs 19) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
  assert (EQ20 : ew (vrd_E regs) 20 = getr regs 20) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)).
  assert (EQ23 : ew (vrd_E regs) 23 = getr regs 23) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 23 23%bv eq_refl)).
  assert (EQ26 : ew (vrd_E regs) 26 = getr regs 26) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
  assert (EQ27 : ew (vrd_E regs) 27 = getr regs 27) by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
  psrr_branch_tok RUN BR HS SHOK vrd_Bspan0.
  + (* taken: p' + j >= text + len, the refusal *)
    cbn [branch_taken] in Hc. unfold bv_ltu in Hc. rewrite HUs', HUe' in Hc.
    apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan0 (vrd_row 326).
    * intros a Ha. destruct Ha as (r & Hin & Hr). cbn [vrd_sa_regions In] in Hin.
      destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
      rewrite E24, Hb24 in Hr.
      right; right; right. exists 0, pos. split; [left; reflexivity|].
      right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Hfb. lia.
    * prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
      prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
      prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
      prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
      prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27. prreg HS (13%bv : bv 5) Q13.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq _ ?mq _) ?mdq) _ =>
        apply (HREF rq mq mdq _ HJ HPM) end.
      -- intros a Ha64 Ha. rewrite <- (HKEEP a Ha64 Ha). unfold aview. f_equal. unfold mbyte.
         rewrite (HFr0 (Z_to_bv 64 a)); [reflexivity|].
         intros (r & Hin & Hr). cbn [vrd_sa_regions In] in Hin. destruct Hin as [<- | []].
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E24, Hb24 in Hr.
         rewrite unsigned_lit_small in Hr by exact Ha64. apply Ha. lia.
      -- exact (vrd_mg_trans _ _ _ HGR HG0).
      -- unfold vrd_kept_regs.
         rewrite Q2, Q3, Q4, Q8, Q9, Q10, Q12, Q18, Q19, Q20, Q23, Q24, Q26, Q27.
         rewrite EQ2, EQ3, EQ4, EQ8, EQ9, EQ10, EQ12, EQ18, EQ19, EQ20, EQ23, E24, EQ26, EQ27.
         repeat split; reflexivity.
      -- rewrite Q21. unfold w64. rewrite <- (YP0m.Z_to_bv64_canon (-1)).
         change (zcanon (-1)) with 18446744073709551615. reflexivity.
      -- rewrite Q22. unfold w64. rewrite <- HU22. symmetry. apply Z_to_bv_bv_unsigned.
      -- rewrite Q13. unfold w64. rewrite <- HU13. symmetry. apply Z_to_bv_bv_unsigned.
      -- exact Hc.
  + (* not taken: the first token byte is in range *)
    cbn [branch_taken] in Hc. unfold bv_ltu in Hc. rewrite HUs', HUe' in Hc.
    apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan0 (vrd_row 163).
    * intros a Ha. destruct Ha as (r & Hin & Hr). cbn [vrd_sa_regions In] in Hin.
      destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
      rewrite E24, Hb24 in Hr.
      right; right; right. exists 0, pos. split; [left; reflexivity|].
      right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Hfb. lia.
    * prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
      prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
      prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
      prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
      prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27. prreg HS (13%bv : bv 5) Q13.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq _ ?mq _) ?mdq) _ =>
        apply (HNXT rq mq mdq _ HJ HPM) end.
      -- intros a Ha64 Ha. rewrite <- (HKEEP a Ha64 Ha). unfold aview. f_equal. unfold mbyte.
         rewrite (HFr0 (Z_to_bv 64 a)); [reflexivity|].
         intros (r & Hin & Hr). cbn [vrd_sa_regions In] in Hin. destruct Hin as [<- | []].
         cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E24, Hb24 in Hr.
         rewrite unsigned_lit_small in Hr by exact Ha64. apply Ha. lia.
      -- exact (vrd_mg_trans _ _ _ HGR HG0).
      -- unfold vrd_kept_regs.
         rewrite Q2, Q3, Q4, Q8, Q9, Q10, Q12, Q18, Q19, Q20, Q23, Q24, Q26, Q27.
         rewrite EQ2, EQ3, EQ4, EQ8, EQ9, EQ10, EQ12, EQ18, EQ19, EQ20, EQ23, E24, EQ26, EQ27.
         repeat split; reflexivity.
      -- rewrite Q21. unfold w64. rewrite <- (YP0m.Z_to_bv64_canon (-1)).
         change (zcanon (-1)) with 18446744073709551615. reflexivity.
      -- rewrite Q22. unfold w64. rewrite <- HU22. symmetry. apply Z_to_bv_bv_unsigned.
      -- rewrite Q13. unfold w64. rewrite <- HU13. symmetry. apply Z_to_bv_bv_unsigned.
      -- exact Hc.
Qed.

(* the old statement, byte-identical: vrd_seg_sa_P at P := fun _ => True *)
Lemma vrd_seg_sa : forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (b p' text len : Z) (Q : world segs -> config -> Prop),
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  In (0, pos) (frames S) ->
  getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
  getr regs 10 = w64 p' -> getr regs 11 = w64 b -> getr regs 12 = w64 (text + len) ->
  0 <= b < 256 -> 4096 <= text -> text <= p' <= text + len -> text + len < 2 ^ 62 ->
  (* the refusal arm (row 162 taken): nothing is left after the sign *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' ->
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (SHADOW_OFF + frame_addr ly 0 pos / 8 <= a < SHADOW_OFF + frame_addr ly 0 pos / 8 + 8) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     vrd_kept_regs regs' regs ->
     getr regs' 21 = w64 (-1) -> getr regs' 22 = w64 (p' + Z.of_nat (vrd_j b)) ->
     getr regs' 13 = w64 (Z.of_nat (vrd_j b)) ->
     text + len <= p' + Z.of_nat (vrd_j b) ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  (* the fall-through at row 163: the first token byte is at s6 = p' + j *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' ->
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (SHADOW_OFF + frame_addr ly 0 pos / 8 <= a < SHADOW_OFF + frame_addr ly 0 pos / 8 + 8) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     vrd_kept_regs regs' regs ->
     getr regs' 21 = w64 (-1) -> getr regs' 22 = w64 (p' + Z.of_nat (vrd_j b)) ->
     getr regs' 13 = w64 (Z.of_nat (vrd_j b)) ->
     p' + Z.of_nat (vrd_j b) < text + len ->
     SRr segs W (cfg_at segs (BASE + vrd_row 163) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 157) regs mem md) Q.
Proof.
intros d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md b p' text len Q
  HJ HinF R24 R10 R11 R12 Hb Htext Hp'r Hlen HREF HNXT.
exact (vrd_seg_sa_P (fun _ => True) (srr_inv_laws_true segs) d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
  W regs mem md b p' text len Q HJ I HinF R24 R10 R11 R12 Hb Htext Hp'r Hlen
  (fun regs' mem' md' k' HJ' _ => HREF regs' mem' md' k' HJ')
  (fun regs' mem' md' k' HJ' _ => HNXT regs' mem' md' k' HJ')).
Qed.

(* ---- the state at row 163 (A 0x86194), rebuilt: s6 is its own atom (22), the first token byte and the one after
   it are the extra atoms 32 / 33, the text window [s6, s6 + nb) is checked by ONE shadow entry (nb = 2 when a
   second byte exists), and the stack slot s1 + 16 (row 192 spills the endptr cell's address there through s1,
   which equals sp at the dispatch) is writable.
   Measured by symbolic execution: every ASan check of rows 163..182 is covered, sh_obls = []. ---- *)
Definition vrd_Bx : sv := SOff 23 0.
Definition vrd_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition vrd_E2 (regs : bvmap 5 word) (c c1 : Z) : env :=
  @Eimg _ A_prog_listing PI_prog_A (Ereg regs [w64 c; w64 c1]).
Definition vrd_163_regions (nb : Z) : smem :=
  [ YP09.mkRegion (Some 22%nat) 0 nb 0 0
      (YP09.mkChunk 0 (CVal 1 (SOff 32 0)) ::
       (if nb =? 2 then [YP09.mkChunk 1 (CVal 1 (SOff 33 0))] else []));
    YP09.mkRegion (Some 9%nat) 0 32 16 24 [] ].
Definition vrd_163_facts : facts := mkFacts
  [ (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 5); (22%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0);
    (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ] [] [].
Definition ss_vrd_163 (nb : Z) : sstate := mkSS (vrd_row 163) sr_atoms (vrd_163_regions nb) None vrd_163_facts.
Definition vrd_SH1 (nb : Z) : list shent := [mkSHE 22 0 nb].

Lemma vrd_kept_mk : forall (regs regs' : bvmap 5 word) (extras : list word) (E : env),
  (forall n, (n < 32)%nat -> ew E n = ew (Ereg regs extras) n) ->
  getr regs' 2 = ew E 2 -> getr regs' 3 = ew E 3 -> getr regs' 4 = ew E 4 ->
  getr regs' 8 = ew E 8 -> getr regs' 9 = ew E 9 -> getr regs' 10 = ew E 10 ->
  getr regs' 12 = ew E 12 -> getr regs' 18 = ew E 18 -> getr regs' 19 = ew E 19 ->
  getr regs' 20 = ew E 20 -> getr regs' 23 = ew E 23 -> getr regs' 24 = ew E 24 ->
  getr regs' 26 = ew E 26 -> getr regs' 27 = ew E 27 ->
  vrd_kept_regs regs' regs.
Proof.
intros regs regs' extras E HE H2 H3 H4 H8 H9 H10 H12 H18 H19 H20 H23 H24 H26 H27.
unfold vrd_kept_regs.
rewrite H2, H3, H4, H8, H9, H10, H12, H18, H19, H20, H23, H24, H26, H27.
rewrite !HE by lia.
repeat split;
  first [ exact (ew_Ereg_nat regs extras 2 2%bv eq_refl) | exact (ew_Ereg_nat regs extras 3 3%bv eq_refl)
        | exact (ew_Ereg_nat regs extras 4 4%bv eq_refl) | exact (ew_Ereg_nat regs extras 8 8%bv eq_refl)
        | exact (ew_Ereg_nat regs extras 9 9%bv eq_refl) | exact (ew_Ereg_nat regs extras 10 10%bv eq_refl)
        | exact (ew_Ereg_nat regs extras 12 12%bv eq_refl) | exact (ew_Ereg_nat regs extras 18 18%bv eq_refl)
        | exact (ew_Ereg_nat regs extras 19 19%bv eq_refl) | exact (ew_Ereg_nat regs extras 20 20%bv eq_refl)
        | exact (ew_Ereg_nat regs extras 23 23%bv eq_refl) | exact (ew_Ereg_nat regs extras 24 24%bv eq_refl)
        | exact (ew_Ereg_nat regs extras 26 26%bv eq_refl) | exact (ew_Ereg_nat regs extras 27 27%bv eq_refl) ].
Qed.

(* the digit test of row 170, as a fact about the byte: `c - 58 <u -10` is exactly `not a digit` *)
Lemma vrd_dig_test : forall x, 0 <= x < 256 -> (zcanon (x - 58) <? 18446744073709551606) = negb (digit x).
Proof.
intros x Hx. unfold zcanon, M64, digit.
destruct (Z_lt_le_dec x 58) as [Hlt|Hge].
- rewrite <- (Z.mod_add (x - 58) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
  destruct (Z_lt_le_dec x 48) as [H48|H48].
  + replace (48 <=? x) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb negb].
    apply Z.ltb_lt. lia.
  + replace (48 <=? x) with true by (symmetry; apply Z.leb_le; lia).
    replace (x <=? 57) with true by (symmetry; apply Z.leb_le; lia). cbn [andb negb].
    apply Z.ltb_ge. lia.
- rewrite Z.mod_small by lia.
  replace (x <=? 57) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite andb_false_r. cbn [negb]. apply Z.ltb_lt. lia.
Qed.

(* the second-byte digit test of row 182 *)
Lemma vrd_dig_test2 : forall x, 0 <= x < 256 -> (zcanon (x - 48) <? 10) = digit x.
Proof.
intros x Hx. unfold zcanon, M64, digit.
destruct (Z_lt_le_dec x 48) as [Hlt|Hge].
- rewrite <- (Z.mod_add (x - 48) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
  replace (48 <=? x) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
  apply Z.ltb_ge. lia.
- rewrite Z.mod_small by lia. replace (48 <=? x) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb]. destruct (Z_le_gt_dec x 57) as [Hle|Hgt].
  + replace (x <=? 57) with true by (symmetry; apply Z.leb_le; lia). apply Z.ltb_lt. lia.
  + replace (x <=? 57) with false by (symmetry; apply Z.leb_gt; lia). apply Z.ltb_ge. lia.
Qed.

Lemma vrd_st_163 : forall (W : world segs) regs mem (nb c c1 s6 sp : Z),
  bv_unsigned (getr regs 22) = s6 -> 4096 <= s6 -> s6 + nb <= 2 ^ 47 - 2 ^ 23 -> (nb = 1 \/ nb = 2) ->
  getr regs 23 = w64 SHADOW_OFF ->
  bv_unsigned (getr regs 9) = sp -> 2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 -> s6 + nb <= sp ->
  val_mem segs (rdW W mem) s6 1 c -> 0 <= c < 256 -> 0 <= c1 < 256 ->
  (nb = 2 -> val_mem segs (rdW W mem) (s6 + 1) 1 c1) ->
  (forall o, 16 <= o < 24 -> writable_at segs (rdW W mem) (sp + o)) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF s6 nb -> amem_range s6 nb ->
  st_ok_pi segs VAL (vrd_E2 regs c c1) (ss_vrd_163 nb)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 163)) mem (seg_rom segs))) /\
  sh_ok segs vrd_Bx (vrd_SH1 nb) (vrd_E2 regs c c1) (rdW W mem).
Proof.
intros W regs mem nb c c1 s6 sp H22 Hs6 Hs6n Hnb R23 H2 Hsp Hal Hts Vc Rc Rc1 Vc1 Wst HRA Ham.
assert (EL : forall n, (n < 32)%nat -> ew (vrd_E2 regs c c1) n = ew (Ereg regs [w64 c; w64 c1]) n)
  by (intros n Hn; unfold vrd_E2; apply Eimg_low; unfold A_TEXT; lia).
assert (E2 : bv_unsigned (ew (vrd_E2 regs c c1) 9) = sp)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H2).
assert (E22 : bv_unsigned (ew (vrd_E2 regs c c1) 22) = s6)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E23 : ew (vrd_E2 regs c c1) 23 = w64 SHADOW_OFF)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew (vrd_E2 regs c c1) 32 = w64 c)
  by (unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (vrd_E2 regs c c1) 33 = w64 c1)
  by (unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + destruct Hnb as [-> | ->]; vm_compute; reflexivity.
  + unfold vrd_163_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      destruct Hnb as [-> | ->]; cbn; repeat constructor.
      -- apply (chunk_ok_val segs _ _ s6 0 1 (SOff 32 0) c);
           [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | cbn; lia | lia | rewrite Z.add_0_r; exact Vc].
      -- apply (chunk_ok_val segs _ _ s6 0 1 (SOff 32 0) c);
           [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | cbn; lia | lia | rewrite Z.add_0_r; exact Vc].
      -- apply (chunk_ok_val segs _ _ s6 1 1 (SOff 33 0) c1);
           [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | cbn; lia | lia | exact (Vc1 eq_refl)].
    * rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. exact (Wst o Ho).
  + apply pairwise_disjoint_of_extents. unfold vrd_163_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
    rewrite E2, E22. unfold zdisj. cbn [fst snd]. repeat split; first [lia | left; lia | right; lia].
  + split; [|split; [exact I | exact I]].
    cbn [vrd_163_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E22, E23, E32, E33. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
    repeat split; try lia; try exact I.
- unfold sh_ok, vrd_SH1. constructor; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 22 s6 nb s6 0 nb HRA).
  + unfold vrd_Bx. rewrite YP0e.U_SOff, E23, Z.add_0_r. unfold w64.
    rewrite unsigned_lit_small by lia. apply YP0m.zcanon_small. lia.
  + rewrite YP0e.U_SOff, E22, Z.add_0_r. apply YP0m.zcanon_small. lia.
  + lia.
  + lia.
  + intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
    destruct Hnb as [-> | ->]; cbn [Z.min Z.max] in Hx; destruct Ham; lia.
Qed.

(* ======================================================================================================== *)
(* ROWS 163..208: the digit test, the leading-zero test, the loop preamble and the token scan.               *)
(* ======================================================================================================== *)

(* ---- pure helpers ---- *)
Lemma vrd_skipn_nth : forall (l : list Z) (k : nat), (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l.
Proof.
induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.

Lemma vrd_rest_cons : forall (tb : list Z) text x, text <= x < text + Z.of_nat (length tb) ->
  rest_atR tb text x = nth (Z.to_nat (x - text)) tb 0 :: rest_atR tb text (x + 1).
Proof.
intros tb text x Hx. unfold rest_atR.
replace (Z.to_nat (x + 1 - text)) with (S (Z.to_nat (x - text))) by lia.
apply vrd_skipn_nth. lia.
Qed.

Lemma vrd_rest_end : forall (tb : list Z) text x, x = text + Z.of_nat (length tb) -> rest_atR tb text x = [].
Proof.
intros tb text x ->. unfold rest_atR.
replace (Z.to_nat (text + Z.of_nat (length tb) - text)) with (length tb) by lia. apply skipn_all.
Qed.

(* the two tests of rows 163..182 on the bytes at s6, as the model's vrd_num_tok makes them *)
Definition vrd_lead_ok (x : list Z) : bool :=
  match x with
  | c :: z => digit c && negb ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end)
  | [] => false
  end.

Lemma vrd_ra_sub : forall (rd : Z -> option Z) (Bz a n a' n' : Z),
  range_addressable rd Bz a n -> a <= a' -> a' + n' <= a + n -> range_addressable rd Bz a' n'.
Proof. intros rd Bz a n a' n' H H1 H2 x Hx. apply H. lia. Qed.

Lemma vrd_ra_kept : forall (rd rd' : Z -> option Z) (Bz a n : Z),
  (forall y, rd' y = rd y) -> range_addressable rd Bz a n -> range_addressable rd' Bz a n.
Proof. intros rd rd' Bz a n HK H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. rewrite HK. auto. Qed.

Lemma vrd_amem_sub : forall a n a' n', amem_range a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> amem_range a' n'.
Proof. intros a n a' n' H H1 H0 H2. unfold amem_range in *. destruct H as [H|[H3 H4]]; [left; lia | right; lia]. Qed.

Lemma vrd_garr8_byte : forall (m : word -> option byte) text (tb : list Z) x,
  garr8 segs m text tb -> text <= x < text + Z.of_nat (length tb) ->
  val_mem segs m x 1 (nth (Z.to_nat (x - text)) tb 0) /\ 0 <= nth (Z.to_nat (x - text)) tb 0 < 256.
Proof.
intros m text tb x HG Hx. destruct (HG (Z.to_nat (x - text)) ltac:(lia)) as [V R].
replace (text + Z.of_nat (Z.to_nat (x - text))) with x in V by lia. split; assumption.
Qed.

Lemma vrd_garr8_kept : forall (W : world segs) (m m' : word -> option byte) text (tb : list Z),
  (forall a, aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  garr8 segs (rdW W m) text tb -> garr8 segs (rdW W m') text tb.
Proof.
intros W m m' text tb HK HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
eapply val_mem_kept; [|exact V]. intros kk _. apply HK.
Qed.

Lemma vrd_sv_eq : forall E x v, YP0e.U E x = v -> sv_denot E x = w64 v.
Proof. intros E x v H. unfold YP0e.U in H. unfold w64. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* a value the symbolic state holds in a chunk of one of its regions *)
Lemma vrd_val_of_st : forall E ss ms (H : word -> bool) (b : option nat) lo hi wlo whi cs off (n : N) ev v,
  st_ok_pi segs VAL E ss (restrict H ms) ->
  In (YP09.mkRegion b lo hi wlo whi cs) (ss_mem ss) -> In (YP09.mkChunk off (CVal n ev)) cs ->
  sv_denot E ev = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem segs (mrestrict H (ms_mem ms)) (base_val E b + off) (N.to_nat n) v.
Proof.
intros E ss ms H b lo hi wlo whi cs off n ev v HS Hr Hc He Hv Hn.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
apply (val_of_chunk_ok segs E _ _ off n ev v); [|exact He|exact Hv|exact Hn].
apply (region_ok_chunk segs E _ (YP09.mkRegion b lo hi wlo whi cs)); [|exact Hc].
eapply mem_ok_region; [exact HM | exact Hr].
Qed.

Lemma vrd_kept_trans : forall r3 r2 r1 : bvmap 5 word,
  vrd_kept_regs r3 r2 -> vrd_kept_regs r2 r1 -> vrd_kept_regs r3 r1.
Proof.
intros r3 r2 r1 H32 H21. unfold vrd_kept_regs in *.
destruct H32 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
destruct H21 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14).
repeat split; congruence.
Qed.

(* the scan's three byte tests (rows 199, 201, 204) in the form the engine's branch conditions take *)
Lemma vrd_dig_test3 : forall x, 0 <= x < 256 -> (zcanon (x + -48) <? zcanon 10) = digit x.
Proof.
intros x R. apply Bool.eqb_prop.
exact (vrd_z256 (fun z => Bool.eqb (zcanon (z + -48) <? zcanon 10) (digit z)) x R ltac:(vm_compute; reflexivity)).
Qed.

Lemma vrd_rng_test : forall x, 0 <= x < 256 -> (zcanon 58 <? zcanon (x + -43)) = negb ((43 <=? x) && (x <=? 101)).
Proof.
intros x R. apply Bool.eqb_prop.
exact (vrd_z256 (fun z => Bool.eqb (zcanon 58 <? zcanon (z + -43)) (negb ((43 <=? z) && (z <=? 101)))) x R
  ltac:(vm_compute; reflexivity)).
Qed.

Lemma vrd_mask_test : forall x, 0 <= x < 256 -> 43 <= x <= 101 ->
  (zcanon (Z.land (zcanon (Z.shiftr (zcanon 288230376218820621) (Z.land (zcanon (x + -43)) 63))) (zcanon 1))
     =? zcanon 0) = negb (vrd_num5 x).
Proof.
intros x R Hr. apply Bool.eqb_prop.
pose proof (vrd_z256 (fun z => implb ((43 <=? z) && (z <=? 101))
  (Bool.eqb (zcanon (Z.land (zcanon (Z.shiftr (zcanon 288230376218820621) (Z.land (zcanon (z + -43)) 63)))
                (zcanon 1)) =? zcanon 0) (negb (vrd_num5 z))))
  x R ltac:(vm_compute; reflexivity)) as H. cbv beta in H.
replace ((43 <=? x) && (x <=? 101))%bool with true in H
  by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
exact H.
Qed.

(* the scan's model: one more numch byte, a stop at a non-numch byte, a stop at the end of the text *)
Lemma vrd_span_step : forall (tb : list Z) text s6 s6',
  text <= s6 < text + Z.of_nat (length tb) -> numch (nth (Z.to_nat (s6 - text)) tb 0) = true -> s6 + 1 <= s6' ->
  span numch (rest_atR tb text (s6 + 1)) =
    (firstn (Z.to_nat (s6' - (s6 + 1))) (rest_atR tb text (s6 + 1)), rest_atR tb text s6') ->
  span numch (rest_atR tb text s6) = (firstn (Z.to_nat (s6' - s6)) (rest_atR tb text s6), rest_atR tb text s6').
Proof.
intros tb text s6 s6' Hs Hn Hle Hsp.
rewrite (vrd_rest_cons tb text s6 Hs). cbn [span]. rewrite Hn, Hsp.
replace (Z.to_nat (s6' - s6)) with (S (Z.to_nat (s6' - (s6 + 1)))) by lia. reflexivity.
Qed.

Lemma vrd_span_stop : forall (tb : list Z) text s6,
  text <= s6 < text + Z.of_nat (length tb) -> numch (nth (Z.to_nat (s6 - text)) tb 0) = false ->
  span numch (rest_atR tb text s6) = (firstn (Z.to_nat (s6 - s6)) (rest_atR tb text s6), rest_atR tb text s6).
Proof.
intros tb text s6 Hs Hn. replace (Z.to_nat (s6 - s6)) with 0%nat by lia. cbn [firstn].
rewrite (vrd_rest_cons tb text s6 Hs). cbn [span]. rewrite Hn. reflexivity.
Qed.

Lemma vrd_span_end : forall (tb : list Z) text s6,
  text <= s6 -> s6 + 1 = text + Z.of_nat (length tb) -> numch (nth (Z.to_nat (s6 - text)) tb 0) = true ->
  span numch (rest_atR tb text s6) =
    (firstn (Z.to_nat (s6 + 1 - s6)) (rest_atR tb text s6), rest_atR tb text (s6 + 1)).
Proof.
intros tb text s6 Hs He Hn. apply vrd_span_step; [lia | exact Hn | lia |].
rewrite (vrd_rest_end tb text (s6 + 1) He), firstn_nil. reflexivity.
Qed.

(* ---- tactics of the two segments ----
   vrd_rl: the region list of a run's pre-state, computed (LESSON 7: the order is the computed one).
   vrd_awr E9: the write premise when the only window is the stack slot [s1 + 16, s1 + 24) (E9 : base = sp).
   vrd_chain E9 Ha64 Hst: a byte outside that slot is unchanged across every run so far (each run's frame_of).
   vrd_awr0 / vrd_chain0: the same with no window at all (the scan writes nothing).
   vrd_grow: presence grows across every run so far. *)
Local Ltac vrd_rl Hin :=
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change l with l' in Hin end;
  cbn [In] in Hin.
Local Ltac vrd_awr E9 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  unfold awr_ok, awr_byte; intros a (r & Hin & Hr); vrd_rl Hin;
  repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?ew_ewset_other in Hr by lia;
  first [ lia | rewrite E9 in Hr; left; lia ].
Local Ltac vrd_awr0 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  unfold awr_ok; intros a (r & Hin & Hr); vrd_rl Hin;
  repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Local Ltac vrd_fr HFx E9 a Ha64 Hst :=
  unfold aview; f_equal; unfold mbyte;
  rewrite (HFx (Z_to_bv 64 a)); [reflexivity|];
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vrd_rl Hin;
  rewrite unsigned_lit_small in Hr by exact Ha64;
  repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?ew_ewset_other in Hr by lia;
  first [ lia | rewrite E9 in Hr; exfalso; apply Hst; lia ].
Local Ltac vrd_chain E9 Ha64 Hst :=
  repeat match goal with
  | HFx : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- aview ?sg ?Hh ?m2 ?a = _ =>
      transitivity (aview sg Hh m1 a); [vrd_fr HFx E9 a Ha64 Hst | clear HFx]
  end; reflexivity.
Local Ltac vrd_fr0 HFx a :=
  unfold aview; f_equal; unfold mbyte;
  rewrite (HFx (Z_to_bv 64 a)); [reflexivity|];
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vrd_rl Hin;
  repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Local Ltac vrd_chain0 :=
  repeat match goal with
  | HFx : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- aview ?sg ?Hh ?m2 ?a = _ =>
      transitivity (aview sg Hh m1 a); [vrd_fr0 HFx a | clear HFx]
  end; reflexivity.
Local Ltac vrd_grow :=
  repeat match goal with
  | HGx : mem_grows (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2) |- mem_grows (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m2) =>
      apply (vrd_mg_trans _ (mrestrict Hh m1)); [clear HGx | exact HGx]
  end; apply mem_grows_refl.
(* after a run: the fourteen untouched registers and s5, against the run's start registers regs *)
Local Ltac vrd_kept_of HS regs EL KR K21 :=
  let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in let Q4 := fresh "Q4" in let Q8 := fresh "Q8" in
  let Q9 := fresh "Q9" in let Q10 := fresh "Q10" in let Q12 := fresh "Q12" in let Q18 := fresh "Q18" in
  let Q19 := fresh "Q19" in let Q20 := fresh "Q20" in let Q23 := fresh "Q23" in let Q24 := fresh "Q24" in
  let Q26 := fresh "Q26" in let Q27 := fresh "Q27" in let Q21 := fresh "Q21" in
  prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
  prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (10%bv : bv 5) Q10;
  prreg HS (12%bv : bv 5) Q12; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19;
  prreg HS (20%bv : bv 5) Q20; prreg HS (23%bv : bv 5) Q23; prreg HS (24%bv : bv 5) Q24;
  prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27; prreg HS (21%bv : bv 5) Q21;
  lazymatch type of Q2 with getr ?rq _ = _ =>
    assert (KR : vrd_kept_regs rq regs)
      by exact (vrd_kept_mk regs _ _ _ EL Q2 Q3 Q4 Q8 Q9 Q10 Q12 Q18 Q19 Q20 Q23 Q24 Q26 Q27);
    assert (K21 : getr rq 21 = getr regs 21)
      by (rewrite Q21, EL by lia; exact (ew_Ereg_nat regs _ 21 21%bv eq_refl))
  end;
  clear Q2 Q3 Q4 Q8 Q9 Q10 Q12 Q18 Q19 Q20 Q23 Q24 Q26 Q27 Q21.

(* row 163's two exits: the refusal at row 326 and the loop head at row 193 *)
Local Ltac vrd_163_ref HS HJ HPM HREF regs EL E9 :=
  let KR := fresh "KR" in let K21 := fresh "K21" in
  vrd_kept_of HS regs EL KR K21; pmkst HS;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq _ ?mq _) ?mdq) _ => apply (HREF rq mq mdq _ HJ HPM) end;
  [ let a := fresh "a" in let Ha64 := fresh "Ha64" in let Hst := fresh "Hst" in
    intros a Ha64 Hst; vrd_chain E9 Ha64 Hst
  | vrd_grow
  | exact KR
  | exact K21
  | idtac ].
Local Ltac vrd_163_nxt HS HJ HPM HNXT regs EL E9 U10E U13E U26E p' jj fr :=
  let KR := fresh "KR" in let K21 := fresh "K21" in
  let Q22 := fresh "Q22" in let Q13 := fresh "Q13" in let Q14 := fresh "Q14" in let Q15 := fresh "Q15" in
  let Q11 := fresh "Q11" in let VSP := fresh "VSP" in
  let V0 := fresh "VSP0" in let V1 := fresh "VSP1" in let V2 := fresh "VSP2" in
  vrd_kept_of HS regs EL KR K21;
  prreg HS (22%bv : bv 5) Q22; prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14;
  prreg HS (15%bv : bv 5) Q15;
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as Q11;
  lazymatch type of Q11 with _ = sv_denot ?Ex (sr_get ?l _) =>
    let e := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with e in Q11 end;
  lazymatch type of HS with st_ok_pi _ _ ?EE ?ssq _ =>
    let l := eval vm_compute in (ss_mem ssq) in
    lazymatch l with context [YP09.mkRegion (Some 9%nat) ?lo ?hi ?wlo ?whi ?cs] =>
      assert (V0 : In (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) (ss_mem ssq))
        by (change (ss_mem ssq) with l; cbn [In]; repeat (first [left; reflexivity | right]));
      assert (V1 : In (YP09.mkChunk 16 (CVal 8 (SOff 26 32))) cs)
        by (cbn [In]; repeat (first [left; reflexivity | right]));
      assert (V2 : sv_denot EE (SOff 26 32) = Z_to_bv 64 (fr + 32))
        by (apply vrd_sv_eq; rewrite YP0e.U_SOff; rewrite ?ew_ewset_other by lia; rewrite U26E;
            apply YP0m.zcanon_small; lia);
      let V3 := fresh "VSP3" in let V4 := fresh "VSP4" in
      assert (V3 : 0 <= fr + 32 < 2 ^ (8 * Z.of_N 8)) by (cbn; lia);
      assert (V4 : Z.of_N 8 <= 8) by (cbn; lia);
      pose proof (vrd_val_of_st EE ssq _ _ (Some 9%nat) lo hi wlo whi cs 16 8 (SOff 26 32) (fr + 32) HS
        V0 V1 V2 V3 V4) as VSP
    end end;
  pmkst HS;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq _ ?mq _) ?mdq) _ => apply (HNXT rq mq mdq _ HJ HPM) end;
  [ let a := fresh "a" in let Ha64 := fresh "Ha64" in let Hst := fresh "Hst" in
    intros a Ha64 Hst; vrd_chain E9 Ha64 Hst
  | vrd_grow
  | cbn [base_val] in VSP; rewrite ?ew_ewset_other in VSP by lia; rewrite E9 in VSP; exact VSP
  | exact KR
  | exact K21
  | rewrite Q22, EL by lia; exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)
  | rewrite Q11; apply vrd_sv_eq; rewrite YP0e.U_SAlu, !YP0e.U_SOff; rewrite ?ew_ewset_other by lia;
    rewrite U10E, U13E, !Z.add_0_r; cbn [zalu_raw];
    rewrite (YP0m.zcanon_small p'), (YP0m.zcanon_small jj) by lia; rewrite YP0m.zcanon_small by lia; lia
  | rewrite Q13; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
  | rewrite Q14; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
  | rewrite Q15; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
  | idtac ].

(* ---- SEGMENT R163, rows 163..192 (A 0x86194..0x86208). Rows 163..170: the first token byte c (at s6, shadow-
   checked) must be a digit, else the refusal at row 326. Rows 171..182: a '0' followed by a digit refuses too;
   row 174 skips the second byte when s6 + 1 = text + len, which is why ONE shadow byte is enough then (nb = 1,
   the not-taken arm of row 174 is refutable) and the second is read only when it exists (nb = 2). Rows 183..192
   build the scan's registers (a1 = a0 + a3 = s6, a3 = 10, a4 = 58, a5 = the numch mask) and spill the endptr
   cell's address fr + 32 at s1 + 16. The two outcomes are vrd_lead_ok of the bytes at s6, the model's own two
   tests (vrd_num_tok). ---- *)
(* the generic-invariant twin, as vrd_seg_sa_P *)
Lemma vrd_seg_163_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (p' jj s6 sp fr text len : Z) (tb : list Z) (Q : world segs -> config -> Prop),
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  P mem ->
  getr regs 22 = w64 s6 -> getr regs 10 = w64 p' -> getr regs 13 = w64 jj -> s6 = p' + jj -> 0 <= p' -> 0 <= jj ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 26 = w64 fr -> 0 <= fr -> fr + 32 < 2 ^ 64 ->
  bv_unsigned (getr regs 9) = sp -> 2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 ->
  spZ regs0 - STK_parse_value d <= sp + 16 -> sp + 24 <= spZ regs0 + e ->
  getr regs 12 = w64 (text + len) -> 4096 <= text <= s6 -> s6 < text + len ->
  text + len <= 2 ^ 47 - 2 ^ 23 -> text + len <= sp -> amem_range text len ->
  garr8 segs (rdW W mem) text tb -> Z.of_nat (length tb) = len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF text len ->
  (forall o, 16 <= o < 24 -> writable_at segs (rdW W mem) (sp + o)) ->
  (* row 326: the first byte is not a digit, or it is a '0' followed by a digit *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' -> P mem' ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 16 <= a < sp + 24) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     vrd_kept_regs regs' regs -> getr regs' 21 = getr regs 21 ->
     vrd_lead_ok (rest_atR tb text s6) = false ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  (* row 193: the loop head, with the scan's registers and row 192's spill *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' -> P mem' ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 16 <= a < sp + 24) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     val_mem segs (rdW W mem') (sp + 16) 8 (fr + 32) ->
     vrd_kept_regs regs' regs -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 ->
     getr regs' 11 = w64 s6 -> getr regs' 13 = w64 10 -> getr regs' 14 = w64 58 ->
     getr regs' 15 = w64 VRD_NUMMASK ->
     vrd_lead_ok (rest_atR tb text s6) = true ->
     SRr segs W (cfg_at segs (BASE + vrd_row 193) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 163) regs mem md) Q.
Proof.
intros P PLAW d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md p' jj s6 sp fr text len tb Q
  HJ HPM R22 R10 R13 Hs6j Hp'0 Hjj R23 R26 Hfr0 Hfr1 H9 Hsp Hal HSP1 HSP2 R12 Htext Hs6e Hend Hsp2 Ham GT Hlen HRA
  Wst HREF HNXT.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (U22 : bv_unsigned (getr regs 22) = s6) by (rewrite R22; apply unsigned_lit_small; lia).
destruct (vrd_garr8_byte _ text tb s6 GT ltac:(lia)) as [Vc Rc].
pose proof (vrd_rest_cons tb text s6 ltac:(lia)) as HR.
set (c := nth (Z.to_nat (s6 - text)) tb 0) in *. clearbody c.
assert (Rc1 : 0 <= nth (Z.to_nat (s6 + 1 - text)) tb 0 < 256).
{ destruct (Z_lt_ge_dec (s6 + 1) (text + len)).
  - exact (proj2 (vrd_garr8_byte _ text tb (s6 + 1) GT ltac:(lia))).
  - rewrite nth_overflow by lia. lia. }
assert (HZ2 : s6 + 1 < text + len ->
   val_mem segs (rdW W mem) (s6 + 1) 1 (nth (Z.to_nat (s6 + 1 - text)) tb 0) /\
   rest_atR tb text (s6 + 1) = nth (Z.to_nat (s6 + 1 - text)) tb 0 :: rest_atR tb text (s6 + 1 + 1)).
{ intros Hn. split; [exact (proj1 (vrd_garr8_byte _ text tb (s6 + 1) GT ltac:(lia))) | apply vrd_rest_cons; lia]. }
set (c1 := nth (Z.to_nat (s6 + 1 - text)) tb 0) in *. clearbody c1.
assert (HEI : img_env VAL A_LIM (vrd_E2 regs c c1)) by (unfold vrd_E2; apply Eimg_env).
assert (EL : forall n, (n < 32)%nat -> ew (vrd_E2 regs c c1) n = ew (Ereg regs [w64 c; w64 c1]) n)
  by (intros n Hn; unfold vrd_E2; apply Eimg_low; unfold A_TEXT; lia).
assert (E9 : bv_unsigned (ew (vrd_E2 regs c c1) 9) = sp)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (U22E : bv_unsigned (ew (vrd_E2 regs c c1) 22) = s6)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact U22).
assert (U12E : bv_unsigned (ew (vrd_E2 regs c c1) 12) = text + len)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), R12; apply unsigned_lit_small; lia).
assert (U10E : bv_unsigned (ew (vrd_E2 regs c c1) 10) = p')
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (U13E : bv_unsigned (ew (vrd_E2 regs c c1) 13) = jj)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl), R13; apply unsigned_lit_small; lia).
assert (U26E : bv_unsigned (ew (vrd_E2 regs c c1) 26) = fr)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl), R26; apply unsigned_lit_small; lia).
assert (U32E : bv_unsigned (ew (vrd_E2 regs c c1) 32) = c)
  by (unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 0);
      apply unsigned_lit_small; lia).
assert (U33E : bv_unsigned (ew (vrd_E2 regs c c1) 33) = c1)
  by (unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 1);
      apply unsigned_lit_small; lia).
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
unfold cfg_at.
destruct (Z_lt_ge_dec (s6 + 1) (text + len)) as [Hnb | Hnb].
- (* nb = 2: the byte after c exists *)
  destruct (HZ2 Hnb) as [Vc1 HZ].
  assert (HRA2 : range_addressable (aview segs (w_H W) mem) SHADOW_OFF s6 2)
    by (apply (vrd_ra_sub _ _ text len); [exact HRA | lia | lia]).
  assert (Ham2 : amem_range s6 2) by (apply (vrd_amem_sub text len); [exact Ham | lia | lia | lia]).
  destruct (vrd_st_163 W regs mem 2 c c1 s6 sp U22 ltac:(lia) ltac:(lia) ltac:(right; reflexivity) R23 H9 Hsp Hal
    ltac:(lia) Vc Rc Rc1 (fun _ => Vc1) Wst HRA2 Ham2) as [HS SHOK].
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
  + vrd_awr E9.
  + psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
    * (* row 170 taken: c is not a digit *)
      rename Hc into H170.
      rewrite YI04.branch_ltu_U, YP0e.U_SOff, YP0e.U_SLit in H170. rewrite ?ew_ewset_other in H170 by lia.
      rewrite U32E, (YP0m.zcanon_small 18446744073709551606) in H170 by lia.
      replace (c + -58) with (c - 58) in H170 by lia. rewrite (vrd_dig_test c Rc) in H170.
      apply negb_true_iff in H170.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 326).
      -- vrd_awr E9.
      -- vrd_163_ref HS HJ HPM HREF regs EL E9. rewrite HR. cbn [vrd_lead_ok]. rewrite H170. reflexivity.
    * rename Hc into H170.
      rewrite YI04.branch_ltu_U, YP0e.U_SOff, YP0e.U_SLit in H170. rewrite ?ew_ewset_other in H170 by lia.
      rewrite U32E, (YP0m.zcanon_small 18446744073709551606) in H170 by lia.
      replace (c + -58) with (c - 58) in H170 by lia. rewrite (vrd_dig_test c Rc) in H170.
      apply negb_false_iff in H170.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
      -- vrd_awr E9.
      -- psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
         ++ (* row 172 taken: c <> '0' *)
            rename Hc into H172.
            rewrite YI04.branch_ne_U, YP0e.U_SOff, YP0e.U_SLit in H172. rewrite ?ew_ewset_other in H172 by lia.
            rewrite U32E, Z.add_0_r, (YP0m.zcanon_small c), (YP0m.zcanon_small 48) in H172 by lia.
            apply negb_true_iff, Z.eqb_neq in H172.
            paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 193).
            ** vrd_awr E9.
            ** vrd_163_nxt HS HJ HPM HNXT regs EL E9 U10E U13E U26E p' jj fr.
               rewrite HR. cbn [vrd_lead_ok]. rewrite H170, (proj2 (Z.eqb_neq c 48) H172). reflexivity.
         ++ (* row 172 not taken: c = '0' *)
            rename Hc into H172.
            rewrite YI04.branch_ne_U, YP0e.U_SOff, YP0e.U_SLit in H172. rewrite ?ew_ewset_other in H172 by lia.
            rewrite U32E, Z.add_0_r, (YP0m.zcanon_small c), (YP0m.zcanon_small 48) in H172 by lia.
            apply negb_false_iff, Z.eqb_eq in H172.
            paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
            ** vrd_awr E9.
            ** psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
               --- (* row 174 taken: refuted, the second byte exists *)
                   exfalso. rename Hc into H174.
                   rewrite YI04.branch_geu_U, !YP0e.U_SOff in H174. rewrite ?ew_ewset_other in H174 by lia.
                   rewrite U22E, U12E, Z.add_0_r, (YP0m.zcanon_small (s6 + 1)), (YP0m.zcanon_small (text + len))
                     in H174 by lia.
                   apply negb_true_iff, Z.ltb_ge in H174. lia.
               --- rename Hc into H174.
                   paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
                   +++ vrd_awr E9.
                   +++ psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
                       *** (* row 182 taken: c1 is a digit, refuse *)
                           rename Hc into H182.
                           rewrite YI04.branch_ltu_U, YP0e.U_SOff, YP0e.U_SLit in H182.
                           rewrite ?ew_ewset_other in H182 by lia.
                           rewrite U33E, (YP0m.zcanon_small 10) in H182 by lia.
                           replace (c1 + -48) with (c1 - 48) in H182 by lia. rewrite (vrd_dig_test2 c1 Rc1) in H182.
                           paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 326).
                           ---- vrd_awr E9.
                           ---- vrd_163_ref HS HJ HPM HREF regs EL E9.
                                rewrite HR, HZ, H172. cbn [vrd_lead_ok]. rewrite H182. reflexivity.
                       *** rename Hc into H182.
                           rewrite YI04.branch_ltu_U, YP0e.U_SOff, YP0e.U_SLit in H182.
                           rewrite ?ew_ewset_other in H182 by lia.
                           rewrite U33E, (YP0m.zcanon_small 10) in H182 by lia.
                           replace (c1 + -48) with (c1 - 48) in H182 by lia. rewrite (vrd_dig_test2 c1 Rc1) in H182.
                           paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 193).
                           ---- vrd_awr E9.
                           ---- vrd_163_nxt HS HJ HPM HNXT regs EL E9 U10E U13E U26E p' jj fr.
                                rewrite HR, HZ, H172. cbn [vrd_lead_ok]. rewrite H182. reflexivity.
- (* nb = 1: c is the text's last byte *)
  assert (HZ : rest_atR tb text (s6 + 1) = []) by (apply vrd_rest_end; lia).
  assert (HRA1 : range_addressable (aview segs (w_H W) mem) SHADOW_OFF s6 1)
    by (apply (vrd_ra_sub _ _ text len); [exact HRA | lia | lia]).
  assert (Ham1 : amem_range s6 1) by (apply (vrd_amem_sub text len); [exact Ham | lia | lia | lia]).
  destruct (vrd_st_163 W regs mem 1 c c1 s6 sp U22 ltac:(lia) ltac:(lia) ltac:(left; reflexivity) R23 H9 Hsp Hal
    ltac:(lia) Vc Rc Rc1 ltac:(intros HH; discriminate HH) Wst HRA1 Ham1) as [HS SHOK].
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
  + vrd_awr E9.
  + psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
    * rename Hc into H170.
      rewrite YI04.branch_ltu_U, YP0e.U_SOff, YP0e.U_SLit in H170. rewrite ?ew_ewset_other in H170 by lia.
      rewrite U32E, (YP0m.zcanon_small 18446744073709551606) in H170 by lia.
      replace (c + -58) with (c - 58) in H170 by lia. rewrite (vrd_dig_test c Rc) in H170.
      apply negb_true_iff in H170.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 326).
      -- vrd_awr E9.
      -- vrd_163_ref HS HJ HPM HREF regs EL E9. rewrite HR. cbn [vrd_lead_ok]. rewrite H170. reflexivity.
    * rename Hc into H170.
      rewrite YI04.branch_ltu_U, YP0e.U_SOff, YP0e.U_SLit in H170. rewrite ?ew_ewset_other in H170 by lia.
      rewrite U32E, (YP0m.zcanon_small 18446744073709551606) in H170 by lia.
      replace (c + -58) with (c - 58) in H170 by lia. rewrite (vrd_dig_test c Rc) in H170.
      apply negb_false_iff in H170.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
      -- vrd_awr E9.
      -- psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
         ++ rename Hc into H172.
            paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 193).
            ** vrd_awr E9.
            ** vrd_163_nxt HS HJ HPM HNXT regs EL E9 U10E U13E U26E p' jj fr.
               rewrite HR, HZ. cbn [vrd_lead_ok]. rewrite H170, andb_false_r. reflexivity.
         ++ rename Hc into H172.
            paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
            ** vrd_awr E9.
            ** psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
               --- rename Hc into H174.
                   paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 193).
                   +++ vrd_awr E9.
                   +++ vrd_163_nxt HS HJ HPM HNXT regs EL E9 U10E U13E U26E p' jj fr.
                       rewrite HR, HZ. cbn [vrd_lead_ok]. rewrite H170, andb_false_r. reflexivity.
               --- (* row 174 not taken: refuted, s6 + 1 = text + len *)
                   exfalso. rename Hc into H174.
                   rewrite YI04.branch_geu_U, !YP0e.U_SOff in H174. rewrite ?ew_ewset_other in H174 by lia.
                   rewrite U22E, U12E, Z.add_0_r, (YP0m.zcanon_small (s6 + 1)), (YP0m.zcanon_small (text + len))
                     in H174 by lia.
                   apply negb_false_iff, Z.ltb_lt in H174. lia.
Qed.

(* the old statement, byte-identical: vrd_seg_163_P at P := fun _ => True *)
Lemma vrd_seg_163 : forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (p' jj s6 sp fr text len : Z) (tb : list Z) (Q : world segs -> config -> Prop),
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  getr regs 22 = w64 s6 -> getr regs 10 = w64 p' -> getr regs 13 = w64 jj -> s6 = p' + jj -> 0 <= p' -> 0 <= jj ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 26 = w64 fr -> 0 <= fr -> fr + 32 < 2 ^ 64 ->
  bv_unsigned (getr regs 9) = sp -> 2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 ->
  spZ regs0 - STK_parse_value d <= sp + 16 -> sp + 24 <= spZ regs0 + e ->
  getr regs 12 = w64 (text + len) -> 4096 <= text <= s6 -> s6 < text + len ->
  text + len <= 2 ^ 47 - 2 ^ 23 -> text + len <= sp -> amem_range text len ->
  garr8 segs (rdW W mem) text tb -> Z.of_nat (length tb) = len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF text len ->
  (forall o, 16 <= o < 24 -> writable_at segs (rdW W mem) (sp + o)) ->
  (* row 326: the first byte is not a digit, or it is a '0' followed by a digit *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 16 <= a < sp + 24) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     vrd_kept_regs regs' regs -> getr regs' 21 = getr regs 21 ->
     vrd_lead_ok (rest_atR tb text s6) = false ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  (* row 193: the loop head, with the scan's registers and row 192's spill *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 16 <= a < sp + 24) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     val_mem segs (rdW W mem') (sp + 16) 8 (fr + 32) ->
     vrd_kept_regs regs' regs -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 ->
     getr regs' 11 = w64 s6 -> getr regs' 13 = w64 10 -> getr regs' 14 = w64 58 ->
     getr regs' 15 = w64 VRD_NUMMASK ->
     vrd_lead_ok (rest_atR tb text s6) = true ->
     SRr segs W (cfg_at segs (BASE + vrd_row 193) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 163) regs mem md) Q.
Proof.
intros d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md p' jj s6 sp fr text len tb Q
  HJ R22 R10 R13 Hs6j Hp'0 Hjj R23 R26 Hfr0 Hfr1 H9 Hsp Hal HSP1 HSP2 R12 Htext Hs6e Hend Hsp2 Ham GT Hlen HRA
  Wst HREF HNXT.
exact (vrd_seg_163_P (fun _ => True) (srr_inv_laws_true segs) d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
  W regs mem md p' jj s6 sp fr text len tb Q HJ I R22 R10 R13 Hs6j Hp'0 Hjj R23 R26 Hfr0 Hfr1 H9 Hsp Hal HSP1 HSP2
  R12 Htext Hs6e Hend Hsp2 Ham GT Hlen HRA Wst
  (fun regs' mem' md' k' HJ' _ => HREF regs' mem' md' k' HJ')
  (fun regs' mem' md' k' HJ' _ => HNXT regs' mem' md' k' HJ')).
Qed.

(* ---- the loop head at row 193 (A 0x8620c), rebuilt each round: s6 is atom 22 and a1 is pinned to it (row 206
   increments both, and the shadow check of rows 193..196 is on a1, the load of row 197 on s6), the three scan
   constants are pinned, the byte c at s6 is the extra atom 32 and ONE shadow entry covers [s6, s6 + 1). No window
   is writable: the scan writes nothing. Measured by symbolic execution: sh_obls = [] on every run. ---- *)
Definition vrd_lp_sr : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 11%bv (SOff 22 0)) 13%bv (SLit 10)) 14%bv (SLit 58)) 15%bv
    (SLit VRD_NUMMASK).
Definition vrd_lp_regions : smem := [ YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition vrd_lp_facts : facts := mkFacts
  [ (22%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition ss_vrd_lp : sstate := mkSS (vrd_row 193) vrd_lp_sr vrd_lp_regions None vrd_lp_facts.
Definition vrd_SHL : list shent := [mkSHE 22 0 1].

Lemma vrd_st_lp : forall (W : world segs) regs mem (c s6 : Z),
  getr regs 22 = w64 s6 -> getr regs 11 = w64 s6 -> getr regs 13 = w64 10 -> getr regs 14 = w64 58 ->
  getr regs 15 = w64 VRD_NUMMASK -> getr regs 23 = w64 SHADOW_OFF ->
  4096 <= s6 -> s6 + 1 <= 2 ^ 47 - 2 ^ 23 ->
  val_mem segs (rdW W mem) s6 1 c -> 0 <= c < 256 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF s6 1 -> amem_range s6 1 ->
  st_ok_pi segs VAL (vrd_E2 regs c 0) ss_vrd_lp
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 193)) mem (seg_rom segs))) /\
  sh_ok segs vrd_Bx vrd_SHL (vrd_E2 regs c 0) (rdW W mem).
Proof.
intros W regs mem c s6 R22 R11 R13 R14 R15 R23 Hs6 Hs6n Vc Rc HRA Ham.
assert (EL : forall n, (n < 32)%nat -> ew (vrd_E2 regs c 0) n = ew (Ereg regs [w64 c; w64 0]) n)
  by (intros n Hn; unfold vrd_E2; apply Eimg_low; unfold A_TEXT; lia).
assert (U22 : bv_unsigned (ew (vrd_E2 regs c 0) 22) = s6)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (E23 : ew (vrd_E2 regs c 0) 23 = w64 SHADOW_OFF)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew (vrd_E2 regs c 0) 32 = w64 c)
  by (unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold vrd_lp_sr.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg| |]| |]| |]| |];
      try (intros X; discriminate X).
    * cbn [sv_denot]. rewrite U22, Z.add_0_r. exact R11.
    * exact R13.
    * exact R14.
    * exact R15.
  + vm_compute. reflexivity.
  + unfold vrd_lp_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ s6 0 1 (SOff 32 0) c);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | rewrite Z.add_0_r; exact Vc].
  + apply pairwise_disjoint_of_extents. unfold vrd_lp_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. tauto.
  + split; [|split; [exact I | exact I]].
    cbn [vrd_lp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U22, E23, E32. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; try lia; try exact I.
- unfold sh_ok, vrd_SHL. constructor; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 22 s6 1 s6 0 1 HRA).
  + unfold vrd_Bx. rewrite YP0e.U_SOff, E23, Z.add_0_r. unfold w64.
    rewrite unsigned_lit_small by lia. apply YP0m.zcanon_small. lia.
  + rewrite YP0e.U_SOff, U22, Z.add_0_r. apply YP0m.zcanon_small. lia.
  + lia.
  + lia.
  + intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
    cbn [Z.min Z.max] in Hx; destruct Ham; lia.
Qed.

(* an exit of the scan at row 267 at s6x: the registers rows 193..266 leave alone, s5, s6 *)
Local Ltac vrd_lp_exit HS HJ HPM HK regs EL R12 R22 s6x :=
  let KR := fresh "KR" in let K21 := fresh "K21" in let Q22 := fresh "Q22" in
  vrd_kept_of HS regs EL KR K21;
  prreg HS (22%bv : bv 5) Q22;
  pmkst HS;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq _ ?mq _) ?mdq) _ => apply (HK rq mq mdq _ s6x HJ HPM) end;
  [ let a := fresh "a" in intros a; vrd_chain0
  | vrd_grow
  | exact KR
  | exact K21
  | first [ rewrite Q22, EL by lia; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22
          | rewrite Q22, EL by lia; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), R12; f_equal; lia ]
  | lia
  | idtac ].

(* ---- THE SCAN, rows 193..208 then 266 (A 0x8620c..0x86248, 0x86330): one round per byte. Row 199 takes a digit;
   otherwise rows 201 / 204 test the byte against '+' .. 'e' and the mask, i.e. numch (vrd_numch_split /
   vrd_mask_num); a numch byte advances s6 and a1 (rows 205..206) and row 207 loops while s6 < text + len. Both
   exits reach row 267: a byte outside numch directly (rows 201 / 204), the end of the text through row 208's
   `j` and row 266's `mv s6, a2`. The exit s6' is where span numch stops (the model's token scan), measured by
   induction on text + len - s6. ---- *)
(* the generic-invariant twin, as vrd_seg_sa_P (the induction carries P) *)
Lemma vrd_loop_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall (n : nat) d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp
    (W : world segs) (regs : bvmap 5 word) mem md k (s6 text len : Z) (tb : list Z)
    (Q : world segs -> config -> Prop),
  Z.of_nat n = text + len - s6 ->
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  P mem ->
  getr regs 22 = w64 s6 -> getr regs 11 = w64 s6 -> getr regs 12 = w64 (text + len) ->
  getr regs 13 = w64 10 -> getr regs 14 = w64 58 -> getr regs 15 = w64 VRD_NUMMASK ->
  getr regs 23 = w64 SHADOW_OFF ->
  4096 <= text <= s6 -> s6 < text + len -> text + len <= 2 ^ 47 - 2 ^ 23 -> amem_range text len ->
  garr8 segs (rdW W mem) text tb -> Z.of_nat (length tb) = len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF text len ->
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' s6' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' -> P mem' ->
     (forall a, aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     vrd_kept_regs regs' regs -> getr regs' 21 = getr regs 21 -> getr regs' 22 = w64 s6' ->
     s6 <= s6' <= text + len ->
     span numch (rest_atR tb text s6) =
       (firstn (Z.to_nat (s6' - s6)) (rest_atR tb text s6), rest_atR tb text s6') ->
     SRr segs W (cfg_at segs (BASE + vrd_row 267) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 193) regs mem md) Q.
Proof.
intros P PLAW n; induction n as [|n IH];
  intros d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp W regs mem md k s6 text len tb Q
  Hn HJ HPM R22 R11 R12 R13 R14 R15 R23 Htext Hs6e Hend Ham GT Hlen HRA HK; [lia|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
destruct (vrd_garr8_byte _ text tb s6 GT ltac:(lia)) as [Vc Rc].
set (c := nth (Z.to_nat (s6 - text)) tb 0) in *.
assert (Hceq : c = nth (Z.to_nat (s6 - text)) tb 0) by reflexivity. clearbody c.
assert (HRA1 : range_addressable (aview segs (w_H W) mem) SHADOW_OFF s6 1)
  by (apply (vrd_ra_sub _ _ text len); [exact HRA | lia | lia]).
assert (Ham1 : amem_range s6 1) by (apply (vrd_amem_sub text len); [exact Ham | lia | lia | lia]).
destruct (vrd_st_lp W regs mem c s6 R22 R11 R13 R14 R15 R23 ltac:(lia) ltac:(lia) Vc Rc HRA1 Ham1) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (vrd_E2 regs c 0)) by (unfold vrd_E2; apply Eimg_env).
assert (EL : forall n, (n < 32)%nat -> ew (vrd_E2 regs c 0) n = ew (Ereg regs [w64 c; w64 0]) n)
  by (intros n0 Hn0; unfold vrd_E2; apply Eimg_low; unfold A_TEXT; lia).
assert (U22E : bv_unsigned (ew (vrd_E2 regs c 0) 22) = s6)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (U12E : bv_unsigned (ew (vrd_E2 regs c 0) 12) = text + len)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), R12; apply unsigned_lit_small; lia).
assert (U32E : bv_unsigned (ew (vrd_E2 regs c 0) 32) = c)
  by (unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 0);
      apply unsigned_lit_small; lia).
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
unfold cfg_at.
paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
- vrd_awr0.
- psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
  + (* row 199 taken: c is a digit *)
    rename Hc into H199.
    rewrite YI04.branch_ltu_U, YP0e.U_SOff, YP0e.U_SLit in H199. rewrite ?ew_ewset_other in H199 by lia.
    rewrite U32E, (vrd_dig_test3 c Rc) in H199.
    assert (HN : numch c = true) by (unfold numch; rewrite H199; reflexivity).
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
    * vrd_awr0.
    * psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
      -- (* row 207 taken: s6 + 1 < text + len, the next round *)
         rename Hc into H207.
         rewrite YI04.branch_ltu_U, !YP0e.U_SOff in H207. rewrite ?ew_ewset_other in H207 by lia.
         rewrite U22E, U12E, Z.add_0_r, (YP0m.zcanon_small (s6 + 1)), (YP0m.zcanon_small (text + len))
           in H207 by lia.
         apply Z.ltb_lt in H207.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 193).
         ++ vrd_awr0.
         ++ vrd_kept_of HS regs EL KR K21.
            prreg HS (22%bv : bv 5) Q22. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
            prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
            prreg HS (23%bv : bv 5) Q23.
            pmkst HS.
            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq _ ?mq _) ?mdq) _ =>
              assert (KALL : forall a, aview segs (w_H W) mq a = aview segs (w_H W) mem a)
                by (let a := fresh "a" in intros a; vrd_chain0);
              assert (GALL : mem_grows (rdW W mem) (rdW W mq)) by vrd_grow;
              eapply (IH d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp W rq mq mdq _ (s6 + 1) text len tb Q)
            end;
              [ lia | exact HJ | exact HPM
              | rewrite Q22, U22E; reflexivity
              | rewrite Q11, U22E; reflexivity
              | rewrite Q12, EL by lia; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12
              | rewrite Q13; reflexivity | rewrite Q14; reflexivity | rewrite Q15; reflexivity
              | rewrite Q23, EL by lia; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23
              | lia | lia | exact Hend | exact Ham
              | exact (vrd_garr8_kept W mem _ text tb KALL GT)
              | exact Hlen
              | exact (vrd_ra_kept _ _ _ _ _ KALL HRA)
              | ].
            intros regs2 mem2 md2 k2 s6' HJb HPMb HKb HGb HKRb R21b R22b Hs6' Hsp2.
            apply (HK regs2 mem2 md2 k2 s6' HJb HPMb).
            ** intros a. rewrite HKb. apply KALL.
            ** exact (vrd_mg_trans _ _ _ GALL HGb).
            ** exact (vrd_kept_trans _ _ _ HKRb KR).
            ** rewrite R21b. exact K21.
            ** exact R22b.
            ** lia.
            ** apply vrd_span_step; [lia | rewrite <- Hceq; exact HN | lia | exact Hsp2].
      -- (* row 207 not taken: s6 + 1 = text + len, out through rows 208 and 266 *)
         rename Hc into H207.
         rewrite YI04.branch_ltu_U, !YP0e.U_SOff in H207. rewrite ?ew_ewset_other in H207 by lia.
         rewrite U22E, U12E, Z.add_0_r, (YP0m.zcanon_small (s6 + 1)), (YP0m.zcanon_small (text + len))
           in H207 by lia.
         apply Z.ltb_ge in H207.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 267).
         ++ vrd_awr0.
         ++ vrd_lp_exit HS HJ HPM HK regs EL R12 R22 (s6 + 1).
            apply vrd_span_end; [lia | lia | rewrite <- Hceq; exact HN].
  + (* row 199 not taken: c is not a digit *)
    rename Hc into H199.
    rewrite YI04.branch_ltu_U, YP0e.U_SOff, YP0e.U_SLit in H199. rewrite ?ew_ewset_other in H199 by lia.
    rewrite U32E, (vrd_dig_test3 c Rc) in H199.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
    * vrd_awr0.
    * psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
      -- (* row 201 taken: c is outside ['+', 'e'], not numch *)
         rename Hc into H201.
         rewrite YI04.branch_ltu_U, YP0e.U_SLit, YP0e.U_SOff in H201. rewrite ?ew_ewset_other in H201 by lia.
         rewrite U32E, (vrd_rng_test c Rc) in H201. apply negb_true_iff in H201.
         assert (HN : numch c = false) by (rewrite (vrd_numch_split c Rc), H199, H201; reflexivity).
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 267).
         ++ vrd_awr0.
         ++ vrd_lp_exit HS HJ HPM HK regs EL R12 R22 s6.
            apply vrd_span_stop; [lia | rewrite <- Hceq; exact HN].
      -- rename Hc into H201.
         rewrite YI04.branch_ltu_U, YP0e.U_SLit, YP0e.U_SOff in H201. rewrite ?ew_ewset_other in H201 by lia.
         rewrite U32E, (vrd_rng_test c Rc) in H201. apply negb_false_iff, andb_prop in H201.
         destruct H201 as [H201a H201b]. apply Z.leb_le in H201a. apply Z.leb_le in H201b.
         paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
         ++ vrd_awr0.
         ++ psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
            ** (* row 204 taken: the mask bit is clear, not numch *)
               rename Hc into H204.
               rewrite YI04.branch_eq_U, !YP0e.U_SAlu, !YP0e.U_SLit, YP0e.U_SOff in H204.
               rewrite ?ew_ewset_other in H204 by lia. rewrite U32E in H204. cbn [zalu_raw] in H204.
               rewrite (vrd_mask_test c Rc ltac:(lia)) in H204. apply negb_true_iff in H204.
               assert (HN : numch c = false)
                 by (rewrite (vrd_numch_split c Rc), H199, H204, andb_false_r; reflexivity).
               paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 267).
               --- vrd_awr0.
               --- vrd_lp_exit HS HJ HPM HK regs EL R12 R22 s6.
                   apply vrd_span_stop; [lia | rewrite <- Hceq; exact HN].
            ** (* row 204 not taken: one of '+' '-' '.' 'E' 'e', numch *)
               rename Hc into H204.
               rewrite YI04.branch_eq_U, !YP0e.U_SAlu, !YP0e.U_SLit, YP0e.U_SOff in H204.
               rewrite ?ew_ewset_other in H204 by lia. rewrite U32E in H204. cbn [zalu_raw] in H204.
               rewrite (vrd_mask_test c Rc ltac:(lia)) in H204. apply negb_false_iff in H204.
               assert (HN : numch c = true).
               { rewrite (vrd_numch_split c Rc), H199, H204.
                 replace ((43 <=? c) && (c <=? 101))%bool with true
                   by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
                 reflexivity. }
               paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
               --- vrd_awr0.
               --- psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
                   +++ rename Hc into H207.
                       rewrite YI04.branch_ltu_U, !YP0e.U_SOff in H207. rewrite ?ew_ewset_other in H207 by lia.
                       rewrite U22E, U12E, Z.add_0_r, (YP0m.zcanon_small (s6 + 1)),
                         (YP0m.zcanon_small (text + len)) in H207 by lia.
                       apply Z.ltb_lt in H207.
                       paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 193).
                       *** vrd_awr0.
                       *** vrd_kept_of HS regs EL KR K21.
                           prreg HS (22%bv : bv 5) Q22. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
                           prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
                           prreg HS (23%bv : bv 5) Q23.
                           pmkst HS.
                           lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq _ ?mq _) ?mdq) _ =>
                             assert (KALL : forall a, aview segs (w_H W) mq a = aview segs (w_H W) mem a)
                               by (let a := fresh "a" in intros a; vrd_chain0);
                             assert (GALL : mem_grows (rdW W mem) (rdW W mq)) by vrd_grow;
                             eapply (IH d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp W rq mq mdq _ (s6 + 1)
                               text len tb Q)
                           end;
                             [ lia | exact HJ | exact HPM
                             | rewrite Q22, U22E; reflexivity
                             | rewrite Q11, U22E; reflexivity
                             | rewrite Q12, EL by lia; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12
                             | rewrite Q13; reflexivity | rewrite Q14; reflexivity | rewrite Q15; reflexivity
                             | rewrite Q23, EL by lia; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23
                             | lia | lia | exact Hend | exact Ham
                             | exact (vrd_garr8_kept W mem _ text tb KALL GT)
                             | exact Hlen
                             | exact (vrd_ra_kept _ _ _ _ _ KALL HRA)
                             | ].
                           intros regs2 mem2 md2 k2 s6' HJb HPMb HKb HGb HKRb R21b R22b Hs6' Hsp2.
                           apply (HK regs2 mem2 md2 k2 s6' HJb HPMb).
                           ---- intros a. rewrite HKb. apply KALL.
                           ---- exact (vrd_mg_trans _ _ _ GALL HGb).
                           ---- exact (vrd_kept_trans _ _ _ HKRb KR).
                           ---- rewrite R21b. exact K21.
                           ---- exact R22b.
                           ---- lia.
                           ---- apply vrd_span_step; [lia | rewrite <- Hceq; exact HN | lia | exact Hsp2].
                   +++ rename Hc into H207.
                       rewrite YI04.branch_ltu_U, !YP0e.U_SOff in H207. rewrite ?ew_ewset_other in H207 by lia.
                       rewrite U22E, U12E, Z.add_0_r, (YP0m.zcanon_small (s6 + 1)),
                         (YP0m.zcanon_small (text + len)) in H207 by lia.
                       apply Z.ltb_ge in H207.
                       paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 267).
                       *** vrd_awr0.
                       *** vrd_lp_exit HS HJ HPM HK regs EL R12 R22 (s6 + 1).
                           apply vrd_span_end; [lia | lia | rewrite <- Hceq; exact HN].
Qed.

(* the old statement, byte-identical: vrd_loop_P at P := fun _ => True *)
Lemma vrd_loop : forall (n : nat) d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp
    (W : world segs) (regs : bvmap 5 word) mem md k (s6 text len : Z) (tb : list Z)
    (Q : world segs -> config -> Prop),
  Z.of_nat n = text + len - s6 ->
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  getr regs 22 = w64 s6 -> getr regs 11 = w64 s6 -> getr regs 12 = w64 (text + len) ->
  getr regs 13 = w64 10 -> getr regs 14 = w64 58 -> getr regs 15 = w64 VRD_NUMMASK ->
  getr regs 23 = w64 SHADOW_OFF ->
  4096 <= text <= s6 -> s6 < text + len -> text + len <= 2 ^ 47 - 2 ^ 23 -> amem_range text len ->
  garr8 segs (rdW W mem) text tb -> Z.of_nat (length tb) = len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF text len ->
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k' s6' : Z),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k' ->
     (forall a, aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     vrd_kept_regs regs' regs -> getr regs' 21 = getr regs 21 -> getr regs' 22 = w64 s6' ->
     s6 <= s6' <= text + len ->
     span numch (rest_atR tb text s6) =
       (firstn (Z.to_nat (s6' - s6)) (rest_atR tb text s6), rest_atR tb text s6') ->
     SRr segs W (cfg_at segs (BASE + vrd_row 267) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 193) regs mem md) Q.
Proof.
intros n d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp W regs mem md k s6 text len tb Q
  Hn HJ R22 R11 R12 R13 R14 R15 R23 Htext Hs6e Hend Ham GT Hlen HRA HK.
exact (vrd_loop_P (fun _ => True) (srr_inv_laws_true segs) n d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp W
  regs mem md k s6 text len tb Q Hn HJ I R22 R11 R12 R13 R14 R15 R23 Htext Hs6e Hend Ham GT Hlen HRA
  (fun regs' mem' md' k' s6' HJ' _ => HK regs' mem' md' k' s6' HJ')).
Qed.

End c.
