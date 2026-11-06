(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the head-amp table layout and the contract and walk of reac_headamp_tx_effective on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* reac_headamp_tx_effective (0x84e64) on the ASan build, and the layout of the
   head-amp table struct reac_headamp_tx that the four table functions share. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaStep PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* struct reac_headamp_tx (include/reac/reac_headamp_tx.h:121-151), as the ASan
   build lays it out: three 48 x 3 byte arrays, then the scalars.
   0..143 value[48][3], 144..287 set[48][3], 288..431 dirty[48][3],
   432 active (4), 436 replay_base (1), 437 replay_width (1), 440 replay_idx (4),
   444 replay_wait (4), 448 replay_set_only (1), 449 scene_base (1),
   450 scene_width (1), 452 resweep_period (4), 456 resweep_wait (4);
   460 bytes in all, 438, 439 and 451 being padding. *)
Definition TX_SIZE : Z := 460.
Definition LAY_TX : layout_t :=
  map (fun i => (Z.of_nat i, 1%N)) (seq 0 432) ++
  [ (432, 4%N); (436, 1%N); (437, 1%N); (440, 4%N); (444, 4%N);
    (448, 1%N); (449, 1%N); (450, 1%N); (452, 4%N); (456, 4%N) ].

(* The field value a byte list gives: the little-endian number of its bytes. *)
Fixpoint le_from (T : list byte) (o : Z) (n : nat) : Z :=
  match n with O => 0 | S n' => tb T o + 256 * le_from T (o + 1) n' end.
Definition lay_vals (lay : layout_t) (T : list byte) : list Z :=
  map (fun f => le_from T (fst f) (N.to_nat (snd f))) lay.
Definition tx_vals (T : list byte) : list Z := lay_vals LAY_TX T.

(* The bytes a layout names. *)
Definition lay_byte (lay : layout_t) (i : Z) : bool :=
  existsb (fun f => (fst f <=? i) && (i <? fst f + Z.of_N (snd f))) lay.
Definition tx_fbyte (i : Z) : bool := lay_byte LAY_TX i.

Lemma tb_range : forall T i, 0 <= tb T i < 256.
Proof.
  intros T i. unfold tb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) T (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma tb_nth : forall T i, Z_to_bv 8 (tb T i) = nth (Z.to_nat i) T (Z_to_bv 8 0).
Proof. intros T i. unfold tb. apply Z_to_bv_bv_unsigned. Qed.

Lemma le_from_range : forall n T o, 0 <= le_from T o n < 2 ^ (8 * Z.of_nat n).
Proof.
  induction n as [|n IH]; intros T o; cbn [le_from].
  - cbn. lia.
  - pose proof (tb_range T o) as Hb. specialize (IH T (o + 1)).
    replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma le_byte_le_from : forall n T o k, (k < n)%nat ->
  YO0f.le_byte (le_from T o n) n k = tb T (o + Z.of_nat k).
Proof.
  induction n as [|n IH]; intros T o k Hk; [lia|].
  pose proof (le_from_range (S n) T o) as Hr.
  unfold YO0f.le_byte. rewrite (Z.mod_small _ _ Hr).
  destruct k as [|k].
  - cbn [le_from]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z.add_0_r.
    pose proof (tb_range T o) as Hb. pose proof (le_from_range n T (o + 1)).
    replace (tb T o + 256 * le_from T (o + 1) n) with (tb T o + le_from T (o + 1) n * 256) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - pose proof (IH T (o + 1) k ltac:(lia)) as IHk.
    unfold YO0f.le_byte in IHk. rewrite (Z.mod_small _ _ (le_from_range n T (o + 1))) in IHk.
    replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite <- Z.shiftr_shiftr by lia.
    replace (Z.shiftr (le_from T o (S n)) 8) with (le_from T (o + 1) n).
    2: { cbn [le_from]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
         pose proof (tb_range T o).
         replace (tb T o + 256 * le_from T (o + 1) n) with (le_from T (o + 1) n * 256 + tb T o) by lia.
         rewrite Z_div_plus_full_l by lia.
         rewrite (Z.div_small (tb T o) 256) by lia. lia. }
    rewrite IHk. f_equal. lia.
Qed.

(* A byte a store leaves in the table: the k-th byte of the stored word. *)
Lemma le4_byte_of_word : forall (v : word) (k : nat), (k < 4)%nat ->
  nth k (Mem.le4 v) (Z_to_bv 8 0) = YP09.byte_of_word v (Z.of_nat k).
Proof.
  intros v k Hk. unfold Mem.le4, YP09.byte_of_word.
  destruct k as [|[|[|[|k]]]]; try lia; cbn [Z_to_le_bytes nth Z.of_nat];
    f_equal; rewrite ?Z.shiftr_div_pow2 by lia; try reflexivity.
Qed.

Lemma le1_byte_of_word : forall (v : word),
  nth 0 (Mem.le1 v) (Z_to_bv 8 0) = YP09.byte_of_word v 0.
Proof.
  intros v. unfold Mem.le1, YP09.byte_of_word. cbn [Z_to_le_bytes nth].
  change (8 * 0) with 0. rewrite ?Z.shiftr_0_r. reflexivity.
Qed.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* The bytes of a layout, read one at a time. *)
Definition fields_at (m : word -> option byte) (a : Z) (lay : layout_t) (T : list byte) : Prop :=
  forall o w, In (o, w) lay -> forall k, (k < N.to_nat w)%nat ->
    mbyte segs m (a + (o + Z.of_nat k)) = Some (nth (Z.to_nat (o + Z.of_nat k)) T (Z_to_bv 8 0)).

Definition bytes_at_lay (m : word -> option byte) (a : Z) (lay : layout_t) (T : list byte) : Prop :=
  forall i, lay_byte lay i = true -> mbyte segs m (a + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0)).

Lemma obj_at_fields : forall lay, lay_widths_ok lay = true ->
  forall m a T, obj_at segs m a lay (lay_vals lay T) <-> fields_at m a lay T.
Proof.
  induction lay as [|[o w] lay IH]; intros Hw m a T.
  - cbn [lay_vals map obj_at]. split; [intros _ o' w' Hin; destruct Hin | intros _; exact I].
  - unfold lay_widths_ok in Hw. cbn [forallb] in Hw. apply andb_prop in Hw as [Hw1 Hw2].
    cbn [fst snd] in Hw1. apply Z.leb_le in Hw1.
    cbn [lay_vals map obj_at fst snd].
    assert (Hfield : field_ok segs m a (o, w) (le_from T o (N.to_nat w)) <->
      (forall k, (k < N.to_nat w)%nat ->
        mbyte segs m (a + (o + Z.of_nat k)) = Some (nth (Z.to_nat (o + Z.of_nat k)) T (Z_to_bv 8 0)))).
    { unfold field_ok. cbn [fst snd]. split.
      - intros [Hv _] k Hk. specialize (Hv k Hk).
        replace (a + (o + Z.of_nat k)) with (a + o + Z.of_nat k) by lia. rewrite Hv.
        rewrite (le_byte_le_from (N.to_nat w) T o k Hk). rewrite tb_nth. reflexivity.
      - intros H. split.
        + intros k Hk. specialize (H k Hk).
          replace (a + o + Z.of_nat k) with (a + (o + Z.of_nat k)) by lia. rewrite H.
          rewrite (le_byte_le_from (N.to_nat w) T o k Hk). rewrite tb_nth. reflexivity.
        + pose proof (le_from_range (N.to_nat w) T o) as Hr.
          rewrite N_nat_Z in Hr. exact Hr. }
    rewrite (IH Hw2 m a T). split.
    + intros [Hf Hr] o' w' Hin k Hk. destruct Hin as [Heq | Hin].
      * injection Heq as <- <-. apply (proj1 Hfield Hf k Hk).
      * exact (Hr o' w' Hin k Hk).
    + intros H. split.
      * apply (proj2 Hfield). intros k Hk. apply (H o w (or_introl eq_refl) k Hk).
      * intros o' w' Hin k Hk. apply (H o' w' (or_intror Hin) k Hk).
Qed.

Lemma fields_bytes_lay : forall lay m a T, fields_at m a lay T <-> bytes_at_lay m a lay T.
Proof.
  intros lay m a T. split.
  - intros H i Hi. unfold lay_byte in Hi. apply existsb_exists in Hi as [[o w] [Hin Hb]].
    cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    specialize (H o w Hin (Z.to_nat (i - o)) ltac:(lia)).
    replace (o + Z.of_nat (Z.to_nat (i - o))) with i in H by lia. exact H.
  - intros H o w Hin k Hk. apply H. unfold lay_byte. apply existsb_exists. exists (o, w).
    split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.

Lemma tx_obj_bytes : forall m a T,
  obj_at segs m a LAY_TX (tx_vals T) <->
  (forall i, tx_fbyte i = true -> mbyte segs m (a + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0))).
Proof.
  intros m a T. unfold tx_vals, tx_fbyte.
  rewrite (obj_at_fields LAY_TX ltac:(vm_compute; reflexivity) m a T).
  exact (fields_bytes_lay LAY_TX m a T).
Qed.

(* One byte of the three arrays, as a one-byte field value. *)
Lemma tx_cell_val : forall m a T i, 0 <= i < 432 ->
  obj_at segs m a LAY_TX (tx_vals T) -> val_mem segs m (a + i) 1 (tb T i).
Proof.
  intros m a T i Hi Ho. apply (proj1 (tx_obj_bytes m a T)) with (i := i) in Ho.
  - intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Ho.
    rewrite <- tb_nth. f_equal. f_equal. unfold YO0f.le_byte.
    change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    change (2 ^ (8 * Z.of_nat 1)) with 256. pose proof (tb_range T i).
    rewrite !Z.mod_small by lia. reflexivity.
  - unfold tx_fbyte, lay_byte. apply existsb_exists. exists (i, 1%N).
    split.
    + apply in_or_app. left. apply in_map_iff. exists (Z.to_nat i).
      split; [f_equal; lia | apply in_seq; lia].
    + cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.

(* The bytes a chunk of a region fixes. *)
Lemma byte_of_region : forall E m n b cs lo hi wlo whi od (w : N) e i,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> 0 <= i < Z.of_N w ->
  mbyte segs m (b + od + i) = Some (YP09.byte_of_word (sv_denot E e) i).
Proof.
  intros E m n b cs lo hi wlo whi od w e i HR Hb Hin Hi.
  unfold region_ok in HR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR.
  destruct HR as (_ & _ & _ & HF). rewrite Hb in HF.
  rewrite Forall_forall in HF. specialize (HF _ Hin).
  unfold chunk_ok in HF. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in HF.
  destruct (HF i Hi) as (bb & Hc & Hm). cbn [cbyte] in Hc. injection Hc as <-. exact Hm.
Qed.

End L.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition A_tx_effectiveP : Z := BASE + AF_reac_headamp_tx_effective.
Definition SBz : Z := 0x7fff8000.
Definition TEFF_STK : Z := 16 + ESTACK.
Definition CBx : sv := SOff 32 0.
Definition EFFspan : Z * Z := (SBz, SBz + 2 ^ 44 - 1).
(* t + ch + (ch << 1) + p, the address the code builds for cell (ch, p). *)
Definition XE : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) (SAlu ALU_SLL (SOff 11 0) (SLit 1))) (SOff 12 0).
Definition eff_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
            (11%nat, mkAF 0 255 0); (12%nat, mkAF 0 255 0);
            (32%nat, mkAF SBz SBz 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ]
          [] [ (XE, SOff 33 0) ].
Definition eff_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32 ].
Definition ss_eff : sstate := mkSS AF_reac_headamp_tx_effective sr_atoms eff_regions None eff_facts.
Definition eff_SH : list shent := [].
Definition RX : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 145 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0)); YP09.mkChunk 144 (CVal 1 (SOff 34 0))].
Definition eff_SH2 : list shent := [ mkSHE 33 0 152 ].
Definition eff_extra (tx ch p : Z) (T : list byte) : list word :=
  map (Z_to_bv 64) [SBz; tx + 3 * ch + p; tb T (144 + 3 * ch + p); tb T (3 * ch + p)].
Definition EE (regs : bvmap 5 word) (tx ch p : Z) (T : list byte) : env :=
  Eimg (Ereg regs (eff_extra tx ch p T)).

Section H.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Definition teff_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (tx ch p : Z) (T : list byte)
  : world SEGS -> config -> Prop :=
  apost_base SEGS B TEFF_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       ly' = ly /\ S' = S /\ W' = W /\ getr regs' 10 = w64 (eff T tx ch p) /\
       obj_at SEGS (mrestrict (w_H W) mem') tx LAY_TX (tx_vals T)).

Definition theadamp_tx_effective_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch0 (tx ch p : Z) (T : list byte),
  afn_pre SEGS B TEFF_STK ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 ch -> getr regs 12 = w64 p ->
  0 <= ch < 256 -> 0 <= p < 256 ->
  In (tx, TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T) ->
  SRr SEGS W (cfg_at SEGS A_tx_effectiveP regs mem md) (teff_post regs ly S W mem md tx ch p T).


Lemma lay_inside_TX : lay_inside LAY_TX 460 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tx_fbyte_range : forall i, tx_fbyte i = true -> 0 <= i < 460.
Proof.
  intros i Hi. unfold tx_fbyte, lay_byte in Hi. apply existsb_exists in Hi as [f [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (proj1 (forallb_forall _ LAY_TX) lay_inside_TX f Hin) as Hf. cbn beta in Hf.
  apply andb_prop in Hf as [F1 F2]. apply Z.leb_le in F1. apply Z.leb_le in F2.
  pose proof (N2Z.is_nonneg (snd f)). lia.
Qed.

Lemma denot_XE : forall E t c pv,
  ew E 10 = Z_to_bv 64 t -> ew E 11 = Z_to_bv 64 c -> ew E 12 = Z_to_bv 64 pv ->
  0 <= t -> 0 <= c < 256 -> 0 <= pv < 256 -> t + 3 * c + pv < 2 ^ 64 ->
  sv_denot E XE = Z_to_bv 64 (t + 3 * c + pv).
Proof.
  intros E t c pv Ht Hc Hpv Ht0 Hcr Hpr Hlt.
  rewrite denot_lit_U. f_equal. unfold XE.
  rewrite !U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 10 t Ht ltac:(lia)), (U_atom E 11 c Hc ltac:(lia)), (U_atom E 12 pv Hpv ltac:(lia)).
  rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
  change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (zcanon_id (t + c)) by (unfold M64; lia).
  rewrite (zcanon_id (c * 2)) by (unfold M64; lia).
  rewrite (zcanon_id (t + c + c * 2)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma eff_entry : forall ly S W (regs : bvmap 5 word) mem md ch0 (tx ch p : Z) (T : list byte),
  afn_pre SEGS B TEFF_STK ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 ch -> getr regs 12 = w64 p ->
  0 <= ch < 256 -> 0 <= p < 256 ->
  In (tx, TX_SIZE) (ablocks B ly S) ->
  st_ok_pi SEGS VAL (EE regs tx ch p T) ss_eff
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_tx_effectiveP) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CBx eff_SH (EE regs tx ch p T) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ch0 tx ch p T HPRE H10 H11 H12 Hch Hp Htx.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : TEFF_STK = 4112) by reflexivity.
  destruct (al_blocks _ _ LAWS ly S W mem md tx TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & _ & _).
  change (req_size TX_SIZE) with 460 in *.
  pose proof (blk_off_imgP B ly S W mem md tx TX_SIZE HAR Htx) as Htximg.
  change (req_size TX_SIZE) with 460 in Htximg.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  pose proof pa_B_ok as HBASE.
  rewrite restrict_mkst_fx.
  set (E := EE regs tx ch p T).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (eff_extra tx ch p T)) n)
    by (intros n Hn; subst E; unfold EE; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 ch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E32 : ew E 32 = Z_to_bv 64 SBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (tx + 3 * ch + p)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (tb T (144 + 3 * ch + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (tb T (3 * ch + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; unfold EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  pose proof (tb_range T (144 + 3 * ch + p)) as Rset. pose proof (tb_range T (3 * ch + p)) as Rval.
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_eff, A_tx_effectiveP. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold eff_regions, stack_region, got_regionP, bcell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
        [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) Ecell) by (pose proof (pa_val_range (A_OBJ 32)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 CBx SBz);
        [cbn [sv_denot CBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBz; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    + apply pairwise_disjoint_of_extents.
      unfold eff_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) Ecell) by (pose proof (pa_val_range (A_OBJ 32)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
      repeat split; lia.
    + split; [|split; [exact I | ]].
      * cbn [eff_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, E10, E11, E12, E32, E34, E35, !unsigned_lit_small by (unfold SBz; lia).
        change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
        revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Htx16 Htx4096 Htxceil Rset Rval Hch Hp.
        clear. unfold SBz. intros. repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [eff_facts f_alias alias_ok]. split; [|exact I].
        cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply (denot_XE E tx ch p E10 E11 E12); try lia.
  - unfold sh_ok, eff_SH. apply Forall_nil.
Qed.


(* The shadow entry the walk uses once the arguments are in range: the 152
   bytes from cell (ch, p) on cover both shadow-byte checks the code makes. *)
Lemma shent_of_block_at : forall ly S (W : world SEGS) mem md Ex (n : nat) (q b sz lo hi : Z),
  AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
  U Ex CBx = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  shent_ok SEGS CBx Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
  intros ly S W mem md Ex n q b sz lo hi HAR Hin HB Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

Lemma eff_keep : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md memF mdF (tx : Z) (T : list byte),
  ajournal SEGS B TEFF_STK (spZ regs) [] ly S W mem md [] ly S W memF mdF 0 ->
  In (tx, TX_SIZE) (ablocks B ly S) ->
  obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T) ->
  obj_at SEGS (mrestrict (w_H W) memF) tx LAY_TX (tx_vals T).
Proof.
  intros ly S W regs mem md memF mdF tx T HJ Hin HO.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply (proj2 (tx_obj_bytes SEGS (mrestrict (w_H W) memF) tx T)).
  intros i Hi. pose proof (tx_fbyte_range i Hi) as Hir.
  rewrite <- (proj1 (tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HO i Hi).
  apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem memF (tx + i)).
  exact (F2 tx TX_SIZE i Hin Hin ltac:(change (req_size TX_SIZE) with 460; lia)
           ltac:(intros X; exact (inFP_nil _ X))).
Qed.

Lemma eff_ret : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md
                       (regsF : bvmap 5 word) memF mdF (tx ch p : Z) (T : list byte),
  ajournal SEGS B TEFF_STK (spZ regs) [] ly S W mem md [] ly S W memF mdF 0 ->
  In (tx, TX_SIZE) (ablocks B ly S) ->
  obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T) ->
  aregs_preserved regs regsF ->
  getr regsF 10 = w64 (eff T tx ch p) ->
  teff_post regs ly S W mem md tx ch p T W
    (mkCfg (mkst regsF (getr regs 1) memF (seg_rom SEGS)) mdF).
Proof.
  intros ly S W regs mem md regsF memF mdF tx ch p T HJ Hin HO HP Hv.
  unfold teff_post, apost_base. exists ly, S, regsF, memF, mdF.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hv | exact (eff_keep ly S W regs mem md memF mdF tx T HJ Hin HO)].
Qed.

Lemma eff_dflt_val : forall E (p : Z), 0 <= p < 256 -> ew E 12 = Z_to_bv 64 p ->
  sv_denot E (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 12 (-2)) (SLit 1)) (SLit 5)) = w64 (dflt p).
Proof.
  intros E p Hp E12.
  assert (HI : U E (SAlu ALU_SLTU (SOff 12 (-2)) (SLit 1))
               = Z.b2z ((p + -2) mod 18446744073709551616 <? 1)).
  { rewrite U_SAlu. cbn [zalu_raw].
    rewrite U_SOff, E12, unsigned_lit_small by lia.
    rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
    unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
    destruct ((p + -2) mod 18446744073709551616 <? 1); cbn [Z.b2z]; apply Z.mod_small; lia. }
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite HI.
  rewrite U_SLit, (zcanon_id 5) by (unfold M64; lia).
  change (Z.land 5 63) with 5.
  rewrite <- (dflt_code_all p ltac:(lia)).
  unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616. apply Z.mod_small.
  destruct ((p + -2) mod 18446744073709551616 <? 1); cbn [Z.b2z];
    rewrite Z.shiftl_mul_pow2 by lia; lia.
Qed.

Ltac eff_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.

Ltac eff_leaf_core HS HJx RETt Wt lyt St regst memt mdt txt cht pt Tt Htxt HTot HAEt Hrat E1t Et v pf gl :=
  let R1 := fresh "R1" in let R10 := fresh "R10" in let mat := fresh "mat" in
  eff_reg HS (1%bv : bv 5) (getr regst 1)
    ltac:(cbn [sv_denot]; rewrite E1t, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) R1;
  eff_reg HS (10%bv : bv 5) v pf R10;
  eapply (RETt Wt _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat; cbn [ms_regs ms_mem]; rewrite R1, Hrat;
  eapply (eff_ret lyt St Wt regst memt mdt _ _ _ txt cht pt Tt);
  [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJx
  | exact Htxt | exact HTot
  | eapply (aregs_preserved_of_st_ok SEGS _ Et _ _ regst (eff_extra txt cht pt Tt) HS);
    [exact HAEt | vm_compute; reflexivity]
  | rewrite R10; f_equal; gl ].

Theorem pb_headamp_tx_effective : theadamp_tx_effective_spec.
Proof.
unfold theadamp_tx_effective_spec.
intros ly S W regs mem md ch0 tx ch p T HPRE H10 H11 H12 Hch Hp Htx HTl HTo.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (eff_entry ly S W regs mem md ch0 tx ch p T HPRE H10 H11 H12 Hch Hp Htx) as [HS SHOK].
pose proof (ajournal_init SEGS B TEFF_STK [] ly S W regs mem md ch0 HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TEFF_STK = 4112) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md tx TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
change (req_size TX_SIZE) with 460 in *.
pose proof (blk_off_imgP B ly S W mem md tx TX_SIZE HAR Htx) as Htximg.
change (req_size TX_SIZE) with 460 in Htximg.
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (tb_range T (144 + 3 * ch + p)) as Rset. pose proof (tb_range T (3 * ch + p)) as Rval.
remember (EE regs tx ch p T) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EE; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (eff_extra tx ch p T)) n)
  by (intros n Hn; subst E; unfold EE; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 ch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (tx + 3 * ch + p)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (tb T (144 + 3 * ch + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (tb T (3 * ch + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (change 242%nat with (A_OBJ 1); subst E; unfold EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E 273%nat = Z_to_bv 64 (VAL (A_OBJ 32)))
  by (change 273%nat with (A_OBJ 32); subst E; unfold EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs (eff_extra tx ch p T)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HUB : U E CBx = SHADOW_OFF)
  by (unfold CBx; rewrite (U_atom E 32 SBz E32) by (unfold SBz; lia); reflexivity).
assert (HU33 : forall c, 0 <= tx + 3 * ch + p + c < 2 ^ 64 -> U E (SOff 33 c) = tx + 3 * ch + p + c).
{ intros c Hc. rewrite U_SOff, E33, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
clear HEdef EL.
unfold cfg_at. change (w64 A_tx_effectiveP) with (Z_to_bv 64 A_tx_effectiveP).
paj_run_tok RUN HS HJ SHOK EFFspan;
  [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
psrr_branch_tok RUN BR HS SHOK EFFspan.
- (* 2 >= p *)
  rewrite branch_geu_U, U_SLit, (zcanon_id 2), (U_atom E 12 p E12) in Hc by (unfold M64; lia).
  apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc. rename Hc into Hp2.
  paj_run_tok RUN HS HJ SHOK EFFspan;
    [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
  psrr_branch_tok RUN BR HS SHOK EFFspan.
  + (* 47 < ch : the default *)
    rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 ch E11) in Hc by (unfold M64; lia).
    apply Z.ltb_lt in Hc. rename Hc into Hch47.
    paj_run_tok RUN HS HJ SHOK EFFspan;
      [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
    eff_leaf_core HS HJ RET W ly S regs mem md tx ch p T Htx HTo HAE Hra E1 E (w64 (dflt p)) ltac:(exact (eff_dflt_val E p ltac:(lia) E12))
      ltac:(symmetry; apply (eff_ch T tx ch p ltac:(lia) ltac:(lia))).
  + (* ch <= 47 : the cell *)
    rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_atom E 11 ch E11) in Hc by (unfold M64; lia).
    apply Z.ltb_ge in Hc. rename Hc into Hch47.
    (* the address of the cell is inside the block *)
    assert (HF33 : afact_ok E 33 (mkAF 4096 140737479966720 0)).
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
    apply (st_ok_pi_add_fact E _ _ 33 _ HS) in HF33. clear HS. rename HF33 into HS.
    lazymatch type of HS with
    | st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
      assert (HO : obj_at SEGS (mrestrict (w_H W) (ms_mem msx)) tx LAY_TX (tx_vals T))
        by (exact (eff_keep ly S W regs mem md (ms_mem msx) _ tx T HJ Htx HTo));
      assert (HR : region_ok SEGS E (ms_mem (restrict Hh msx)) RX);
      [ cbn [restrict ms_mem];
        unfold RX, region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
        rewrite E33, unsigned_lit_small by lia;
        split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        apply Forall_cons;
        [ apply (chunk_ok_val SEGS E _ (tx + 3 * ch + p) 0 1 (SOff 35 0) (tb T (3 * ch + p)));
          [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
          replace (tx + 3 * ch + p + 0) with (tx + (3 * ch + p)) by lia;
          exact (tx_cell_val SEGS _ tx T (3 * ch + p) ltac:(lia) HO)
        | apply Forall_cons;
          [ apply (chunk_ok_val SEGS E _ (tx + 3 * ch + p) 144 1 (SOff 34 0) (tb T (144 + 3 * ch + p)));
            [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
            replace (tx + 3 * ch + p + 144) with (tx + (144 + 3 * ch + p)) by lia;
            exact (tx_cell_val SEGS _ tx T (144 + 3 * ch + p) ltac:(lia) HO)
          | apply Forall_nil ] ]
      | pose proof (st_ok_pi_add_region E ssx (restrict Hh msx) RX HS
                      ltac:(vm_compute; reflexivity) HR
                      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
                              let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
                            cbn [all_disjoint]; unfold extent_disjoint, RX;
                            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
                            rewrite ?E33, ?Egot, ?Ecell, ?E2;
                            rewrite !unsigned_lit_small by
                              (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 32)); lia);
                            change (bv_unsigned (getr regs 2)) with (spZ regs);
                            revert Hslo Hceil Htxceil Htx4096 Htximg HcellR HgotR Hch47 Hp2 Hch Hp C1 C3 WS;
                            clear; unfold off_img; intros;
                            repeat match goal with |- _ /\ _ => split end;
                            first [exact I | lia])) as HS2;
        clear HS HO HR; rename HS2 into HS ]
    end.
    lazymatch type of HS with
    | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      assert (SHOK2 : sh_ok SEGS CBx eff_SH2 E (mrestrict (w_H W) (ms_mem msx)));
      [ unfold sh_ok, eff_SH2; apply Forall_cons;
        [ eapply (shent_of_block_at ly S W (ms_mem msx) _ E 33 (tx + 3 * ch + p) tx TX_SIZE 0 152
                    (proj1 HJ) Htx HUB);
          [rewrite (HU33 0) by lia; lia | lia | lia | change (req_size TX_SIZE) with 460; lia]
        | apply Forall_nil ]
      | ] end.
    clear SHOK. rename SHOK2 into SHOK.
    paj_run_tok RUN HS HJ SHOK EFFspan;
      [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
    psrr_branch_tok RUN BR HS SHOK EFFspan.
    * (* the cell was never set : the default *)
      rewrite branch_eq_U, (U_atom E 34 (tb T (144 + 3 * ch + p)) E34), U_lit in Hc by lia.
      apply Z.eqb_eq in Hc. rename Hc into Hset.
      paj_run_tok RUN HS HJ SHOK EFFspan;
        [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
      eff_leaf_core HS HJ RET W ly S regs mem md tx ch p T Htx HTo HAE Hra E1 E (w64 (dflt p)) ltac:(exact (eff_dflt_val E p ltac:(lia) E12))
        ltac:(rewrite (eff_cell T tx ch p ltac:(lia) ltac:(lia) ltac:(lia));
              rewrite (proj2 (Z.eqb_eq (tb T (144 + 3 * ch + p)) 0) Hset); reflexivity).
    * (* the cell was set : its value *)
      rewrite branch_eq_U, (U_atom E 34 (tb T (144 + 3 * ch + p)) E34), U_lit in Hc by lia.
      apply Z.eqb_neq in Hc. rename Hc into Hset.
      paj_run_tok RUN HS HJ SHOK EFFspan;
        [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
      eff_leaf_core HS HJ RET W ly S regs mem md tx ch p T Htx HTo HAE Hra E1 E (w64 (tb T (3 * ch + p)))
        ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(rewrite (eff_cell T tx ch p ltac:(lia) ltac:(lia) ltac:(lia));
              rewrite (proj2 (Z.eqb_neq (tb T (144 + 3 * ch + p)) 0) Hset); reflexivity).
- (* p > 2 : zero *)
  rewrite branch_geu_U, U_SLit, (zcanon_id 2), (U_atom E 12 p E12) in Hc by (unfold M64; lia).
  apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc. rename Hc into Hp2.
  paj_run_tok RUN HS HJ SHOK EFFspan;
    [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
  eff_leaf_core HS HJ RET W ly S regs mem md tx ch p T Htx HTo HAE Hra E1 E (w64 0) ltac:(cbn [sv_denot]; reflexivity)
    ltac:(symmetry; apply (eff_p3 T tx ch p ltac:(lia))).
Qed.

End H.
End F.
End D.
