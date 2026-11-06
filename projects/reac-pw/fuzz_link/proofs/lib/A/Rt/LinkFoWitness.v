(* Satisfiability witness of the function-specific premises of afmemopen_w_spec (LinkFoSpec.v) at link's instance
   (tfibsegs, PcapB, link_amf, link_asink_head), at the state of mark_quietly's call 0x88410 on the first mark of a
   run: a0 = g_said 0x62fee0, a1 = 4096, a2 = "w" 0x21260; __libc.threaded (0x651ea1), __libc.need_locks (0x651ea3),
   ofl_lock (0x652300, 4 bytes) and the open-file list head (0x652308, 8 bytes) all 0; every other byte, the mode word
   at 0x21260, musl's "rwa\0" at 0x20291 and __strchrnul's constants [0x10360, 0x10380) included, the image's (the
   witness memory holds nothing there, so mbyte reads the image). Also: the head law, the frame chain's spine (the
   chain is empty at the call: s0 is mark_quietly's second argument, 0x883e8 `mv s0, a1`), the two universe rows of
   fmemopen's malloc (the image's universe holds [0x5436c] and [0x5436c; 0x96ab8], ACej.v TRACES_fmemopen), and the
   meter room under the frame's trivial meter. The rest of the precondition (afn_pre: AR at a state of the run, the
   stack window; the event and live-byte room) needs AR of image A's run, which only the start-up theorem gives; it
   is written out at the real call state in the lane's report. Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YP03 YI00 YI04 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YG0f YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require ACej ACejUniv.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkFoSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Definition FO_THR : Z := 0x651ea1.   (* amf_threaded link_amf *)
Definition FO_NL : Z := 0x651ea3.    (* amf_need_locks link_amf *)
Definition FO_LOCK : Z := 0x652300.  (* amf_ofl_lock link_amf *)
Definition FO_HEAD : Z := 0x652308.  (* amf_ofl_head link_amf *)

Lemma fo_addrs : amf_threaded link_amf = FO_THR /\ amf_need_locks link_amf = FO_NL /\
  amf_ofl_lock link_amf = FO_LOCK /\ amf_ofl_head link_amf = FO_HEAD.
Proof. repeat split; reflexivity. Qed.

(* a in [lo, lo + n) *)
Definition fo_in (a lo n : Z) : bool := (lo <=? a) && (a <? lo + n).

(* the stdio words and the head, 0; nothing else (mbyte then reads the image) *)
Definition fo_hit (a : Z) : bool := fo_in a FO_THR 1 || fo_in a FO_NL 1 || fo_in a FO_LOCK 4 || fo_in a FO_HEAD 8.
Definition fo_mem : word -> option byte := fun w => if fo_hit (bv_unsigned w) then Some (Z_to_bv 8 0) else None.

Lemma fo_mem_none : forall a, 0 <= a < 2 ^ 64 ->
  ~ (FO_THR <= a < FO_THR + 1) -> ~ (FO_NL <= a < FO_NL + 1) -> ~ (FO_LOCK <= a < FO_LOCK + 4) ->
  ~ (FO_HEAD <= a < FO_HEAD + 8) ->
  fo_mem (Z_to_bv 64 a) = None.
Proof.
  intros a Ha H1 H2 H3 H4. unfold fo_mem. rewrite unsigned_lit_small by lia.
  unfold fo_hit, fo_in.
  repeat match goal with
  | |- context [?lo <=? a] => destruct (Z.leb_spec lo a)
  | |- context [a <? ?hi] => destruct (Z.ltb_spec a hi)
  end; cbn [andb orb]; first [reflexivity | exfalso; lia].
Qed.

Lemma fo_mem_zero : forall a, 0 <= a < 2 ^ 64 ->
  (FO_THR <= a < FO_THR + 1) \/ (FO_NL <= a < FO_NL + 1) \/ (FO_LOCK <= a < FO_LOCK + 4) \/
  (FO_HEAD <= a < FO_HEAD + 8) ->
  fo_mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof.
  intros a Ha H. unfold fo_mem. rewrite unsigned_lit_small by lia.
  unfold fo_hit, fo_in.
  repeat match goal with
  | |- context [?lo <=? a] => destruct (Z.leb_spec lo a)
  | |- context [a <? ?hi] => destruct (Z.ltb_spec a hi)
  end; cbn [andb orb]; first [reflexivity | exfalso; lia].
Qed.

(* an image byte: no witness store there *)
Lemma fo_mbyte_img : forall a, 0 <= a < 0x651ea0 -> mbyte tfibsegs fo_mem a = seg_rom tfibsegs (Z_to_bv 64 a).
Proof.
  intros a Ha. unfold mbyte. rewrite fo_mem_none by (unfold FO_THR, FO_NL, FO_LOCK, FO_HEAD; lia). reflexivity.
Qed.

Lemma fo_val0 : forall a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, (k < n)%nat ->
     (FO_THR <= a + Z.of_nat k < FO_THR + 1) \/ (FO_NL <= a + Z.of_nat k < FO_NL + 1) \/
     (FO_LOCK <= a + Z.of_nat k < FO_LOCK + 4) \/ (FO_HEAD <= a + Z.of_nat k < FO_HEAD + 8)) ->
  val_mem tfibsegs fo_mem a n 0.
Proof.
  intros a n H0 H1 Hin k Hk. unfold mbyte. rewrite fo_mem_zero by (try lia; exact (Hin k Hk)).
  rewrite amf_le_byte_0. reflexivity.
Qed.

(* the three stdio words and the head are 0 *)
Lemma fo_env : amf_env tfibsegs link_amf fo_mem.
Proof.
  unfold amf_env. destruct fo_addrs as (E1 & E2 & E3 & _). rewrite E1, E2, E3.
  split; [|split]; apply fo_val0; unfold FO_THR, FO_NL, FO_LOCK, FO_HEAD; try lia;
    intros k Hk; cbn in Hk; lia.
Qed.

Lemma fo_head : val_mem tfibsegs fo_mem (amf_ofl_head link_amf) 8 0.
Proof.
  destruct fo_addrs as (_ & _ & _ & E4). rewrite E4.
  apply fo_val0; unfold FO_THR, FO_NL, FO_LOCK, FO_HEAD; lia.
Qed.

(* an image byte, from its value (the comparison is on numbers, not on byte records) *)
Lemma fo_rom_byte : forall a v, option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)) = Some (v mod 256) ->
  seg_rom tfibsegs (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros a v H. destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [b|]; [|discriminate].
  cbn in H. injection H as H. f_equal. apply bv_eq. rewrite H, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. reflexivity.
Qed.

(* the mode word at 0x21260: 77 00 00 00 00 00 00 00 in the image *)
Lemma fo_mode : val_mem tfibsegs fo_mem LA_MODE_W 8 119.
Proof.
  intros k Hk. rewrite fo_mbyte_img by (unfold LA_MODE_W; lia).
  do 8 (destruct k as [|k]; [apply fo_rom_byte; vm_compute; reflexivity|]). lia.
Qed.

(* musl's "rwa\0" at 0x20291 *)
Lemma fo_rwa : garr8 tfibsegs fo_mem LA_RWA rwa_Z.
Proof.
  intros j Hj. cbn [length rwa_Z] in Hj.
  split; [| do 4 (destruct j as [|j]; [cbn; lia|]); lia].
  intros k Hk. assert (k = 0%nat) by lia. subst k.
  rewrite fo_mbyte_img by (unfold LA_RWA; lia).
  do 4 (destruct j as [|j]; [apply fo_rom_byte; vm_compute; reflexivity|]). lia.
Qed.

(* __strchrnul's constant window reads the image *)
Lemma fo_mc : forall a, 0x10360 <= a < 0x10380 ->
  amf_rd tfibsegs fo_mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof. intros a Ha. unfold amf_rd. rewrite fo_mbyte_img by lia. reflexivity. Qed.

(* afm_w_args at the call state, for every register file holding the three arguments *)
Theorem afm_w_args_sat : forall regs : bvmap 5 word,
  getr regs 10 = w64 0x62fee0 -> getr regs 11 = w64 4096 -> getr regs 12 = w64 0x21260 ->
  afm_w_args tfibsegs link_amf 0x10360 0x10380 regs fo_mem.
Proof.
  intros regs G10 G11 G12. unfold afm_w_args.
  split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
  split; [exact fo_mode|]. split; [exact fo_rwa|]. split; [exact fo_mc|].
  split; [exact fo_env | exact fo_head].
Qed.

(* the head law, the empty chain's spine, the universe rows (CTX = [[]], ra = 0x96ab8), and the trivial meter, for
   every asyms record with link's code table and trace universe (PcapB, AD2l.v: as_code := Tfib_code,
   as_universe := Tfib_univ, both by reflexivity) *)
Theorem afm_w_rest_sat : forall (B : asyms) S,
  as_code B = Tfib_code -> as_universe B = ACejUniv.Tfib_univ ->
  @amf_head_law link_asink_head link_amf /\
  In (YCbq.spine []) [[]] /\
  In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c [[]] -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (LA_FM_MALLOC_RA :: c)))
     (as_universe B)) /\
  mo_ok ameter_triv S (mo_malloc ameter_triv AMF_BLOCK).
Proof.
  intros B S HC HU. rewrite HC, HU. rewrite ACejUniv.Tfib_univ_fix.
  split; [exact link_amf_head_law|]. split; [left; reflexivity|].
  split; [apply ACej.memZL_In; vm_compute; reflexivity|].
  split; [|exact I].
  intros c [<- | []]. apply ACej.memZL_In. vm_compute. reflexivity.
Qed.

Print Assumptions afm_w_args_sat.
Print Assumptions afm_w_rest_sat.
