(* reac-pw/fuzz_link, image A: the image facts the walk of kernel (0x83d30) needs beyond kernel_acontract's
   premises. kernel_c.v's kernel_apre states nl_errno.e, msg_build.codes, texts, .str.1, .str.8 and long_alias. The
   code also reads four .rodata objects at constant addresses, through `arodata_okP` of apre (their bytes are
   `seg_rom segs`, and segs is a parameter of the contract):
   - the jump table of msg_build's switch, 0x20f78 (listing object A_OBJ 16): `lw a4, 0(a4)` +0x6c4 at
     0x20f78 + 4 (kind & 7), then `add a4, a4, a5` and `jr a4` +0x6cc. Its 8 words (signed offsets from 0x20f78,
     read from the pin's PT_LOAD 0x10000..0x3026c, flags R) give the targets +0x6e4 (kinds 0, 7), +0x6d0 (1),
     +0x1178 (2), +0x1150 (3), +0x11e4 (4), +0x120c (5), +0x11c0 (6);
   - the three magic multipliers: 0x10380 (A_OBJ 11) = 0x2aaaaaaaaaaaaaab, `ld` +0x4cc (byte % 6, spilled to
     0xb8(s1)); 0x10310 (A_OBJ 17) = 0x3333333333333334, `ld` +0x9c0 (byte % 5); 0x10318 (A_OBJ 18) =
     0x1745d1745d1745d2, `ld` +0xa34 (x / 11).
   `KernImg segs B` says, by computation over the abstract segments and asyms, that every byte of the four objects
   lies in a read-only segment, outside the runtime's statics and errno, and that seg_rom gives it. The walk takes it
   as the Section hypothesis `KI`; kernel_img_tfib.v closes it at the image (tfibsegs, PcapB). With apre's
   `arodata_okP`, `ki_*_val_mem` give the `val_mem` facts the engine's regions over these objects need.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK04 YP09 YI04 YG0v YG00 YG0f YG0n YG0d YM05 YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK1d PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition KI_JT : Z := 0x20f78.
Definition ki_jt_words : list Z := [0x6349c; 0x63488; 0x63f30; 0x63f08; 0x63f9c; 0x63fc4; 0x63f78; 0x6349c].
Definition KI_M6 : Z := 0x10380.
Definition KI_M6_V : Z := 0x2aaaaaaaaaaaaaab.
Definition KI_M5 : Z := 0x10310.
Definition KI_M5_V : Z := 0x3333333333333334.
Definition KI_M11 : Z := 0x10318.
Definition KI_M11_V : Z := 0x1745d1745d1745d2.
(* the texts table (.data.rel.ro 0xa17c0, in PT_GNU_RELRO) and its 11 words, the addresses of fuzz_link.c:121-122's
   strings (read from the pin's PT_LOAD with pyelftools) *)
Definition KI_TX : Z := 0xa17c0.
Definition ki_tx_words : list Z :=
  [0x20fc0; 0x21100; 0x21120; 0x21140; 0x21160; 0x21180; 0x211a0; 0x211c0; 0x211e0; 0x21200; 0x21220].
(* the 12 strings kernel hands to attr_text (the 11 texts, .str.8 0x210c0; texts[0] is .str.1 0x20fc0), each with
   its NUL: "", "reac-pw:served", "reac-pw:minted", "host-alias", "reac-pw:", "reac-pw:served2", "reac-pw", "vlan",
   "veth", "vlanx", "vla", "x" *)
Definition ki_strs : list (Z * list Z) :=
  [(0x20fc0, [0]);
   (0x21100, [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100; 0]);
   (0x21120, [114; 101; 97; 99; 45; 112; 119; 58; 109; 105; 110; 116; 101; 100; 0]);
   (0x21140, [104; 111; 115; 116; 45; 97; 108; 105; 97; 115; 0]);
   (0x21160, [114; 101; 97; 99; 45; 112; 119; 58; 0]);
   (0x21180, [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100; 50; 0]);
   (0x211a0, [114; 101; 97; 99; 45; 112; 119; 0]);
   (0x211c0, [118; 108; 97; 110; 0]);
   (0x211e0, [118; 101; 116; 104; 0]);
   (0x21200, [118; 108; 97; 110; 120; 0]);
   (0x21220, [118; 108; 97; 0]);
   (0x210c0, [120; 0])].

(* the jump table's target of kind & 7 = i, as an offset from kernel's entry 0x83d30 *)
Definition ki_jt_target (i : nat) : Z := KI_JT + nth i ki_jt_words 0 - 0x83d30.
Lemma ki_jt_targets :
  map ki_jt_target (seq 0 8) = [0x6e4; 0x6d0; 0x1178; 0x1150; 0x11e4; 0x120c; 0x11c0; 0x6e4].
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* one byte: in a read-only segment, not a runtime static, not errno, and seg_rom gives v *)
Definition ki_ro_ok (segs : list Segment) (B : asyms) (a v : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a)
                    && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs
  && negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static B))
  && negb ((as_errno B <=? a) && (a <? as_errno B + 4))
  && match seg_rom segs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end.

(* the w-byte little-endian words ws from a, byte by byte *)
Definition ki_words_ok (segs : list Segment) (B : asyms) (a : Z) (w : nat) (ws : list Z) : bool :=
  forallb (fun i => forallb (fun k => ki_ro_ok segs B (a + Z.of_nat w * Z.of_nat i + Z.of_nat k)
                                         (le_byte (nth i ws 0) w k)) (seq 0 w)) (seq 0 (length ws)).

(* no non-writable segment meets [lo, lo + n) *)
Definition ki_nro (segs : list Segment) (lo n : Z) : bool :=
  forallb (fun s => seg_writable s || (lo + n <=? Z.of_N (seg_base s)) ||
                    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? lo)) segs.

(* every loaded segment lies in [0x10000, pcap_img_end) (LinkWalkShadow.v's `segs_img`) *)
Definition ki_img_bounds (segs : list Segment) : bool :=
  forallb (fun s => (Z.of_N (seg_size s) =? 0) ||
                    ((0x10000 <=? Z.of_N (seg_base s)) &&
                     (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? pcap_img_end))) segs.

(* one relro byte (PcapRelro.v's window [0xa1380, 0xa26c8): in_roP's second arm): not a runtime static, not errno,
   and seg_rom gives v *)
Definition ki_rel_ok (segs : list Segment) (B : asyms) (a v : Z) : bool :=
  (0xa1380 <=? a) && (a <? 0xa26c8)
  && negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static B))
  && negb ((as_errno B <=? a) && (a <? as_errno B + 4))
  && match seg_rom segs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end.
Definition ki_rwords_ok (segs : list Segment) (B : asyms) (a : Z) (w : nat) (ws : list Z) : bool :=
  forallb (fun i => forallb (fun k => ki_rel_ok segs B (a + Z.of_nat w * Z.of_nat i + Z.of_nat k)
                                         (le_byte (nth i ws 0) w k)) (seq 0 w)) (seq 0 (length ws)).
(* the bytes of the strings, each read-only with its value *)
Definition ki_strs_ok (segs : list Segment) (B : asyms) : bool :=
  forallb (fun ps => forallb (fun i => ki_ro_ok segs B (fst ps + Z.of_nat i) (nth i (snd ps) 0))
                              (seq 0 (length (snd ps)))) ki_strs.
(* The four .rodata objects (their bytes read-only, outside the runtime's statics and errno, seg_rom gives them);
   kernel's two image write ranges, g_nl (the whole object) and long_alias, in writable segments and met by no
   non-writable one; the relro window [PCAP_RLO, PCAP_RHI) inside one segment; every segment inside the image; the
   texts table's 11 words (relro) and the 12 strings' bytes; and seg_rom defined on all of the image, so that every
   image byte is visible at every memory (ki_vis: the slack after a string's NUL, which attr_text's Pre asks to be
   readable, is no read-set byte). With these `arodata_okP` moves across kernel's own writes (a write into G meets
   no read-only byte, and every read-only byte is an image byte, which akept's image clause keeps), and
   aj_gx_intrin_at gets its destination's writability (link_ajkit.v wseg_LA_G_NL / wseg_LA_LONG_ALIAS at
   tfibsegs). *)
Record KernImg (segs : list Segment) (B : asyms) : Prop := mkKernImg {
  ki_jt : ki_words_ok segs B KI_JT 4 ki_jt_words = true;
  ki_m6 : ki_words_ok segs B KI_M6 8 [KI_M6_V] = true;
  ki_m5 : ki_words_ok segs B KI_M5 8 [KI_M5_V] = true;
  ki_m11 : ki_words_ok segs B KI_M11 8 [KI_M11_V] = true;
  ki_gnl : wseg_ok segs (Z_to_bv 64 0x5dcac0) (Z.to_nat 271992) = true;
  ki_la : wseg_ok segs (Z_to_bv 64 0x62fd40) (Z.to_nat 301) = true;
  ki_gnl_nro : ki_nro segs 0x5dcac0 271992 = true;
  ki_la_nro : ki_nro segs 0x62fd40 301 = true;
  ki_relro : existsb (relro_in_seg 0xa1380 0xa26c8) segs = true;
  ki_img : ki_img_bounds segs = true;
  ki_tx : ki_rwords_ok segs B KI_TX 8 ki_tx_words = true;
  ki_str : ki_strs_ok segs B = true;
  ki_rom : forall a, 0x10000 <= a < pcap_img_end -> seg_rom segs (Z_to_bv 64 a) <> None
}.

Lemma ki_segs_img : forall segs B, KernImg segs B -> forall a, in_img segs a -> 0x10000 <= a < pcap_img_end.
Proof.
  intros segs B KI a (s & Hin & Ha). pose proof (ki_img segs B KI) as H. unfold ki_img_bounds in H.
  rewrite forallb_forall in H. specialize (H s Hin).
  apply orb_prop in H as [H|H].
  - apply Z.eqb_eq in H. lia.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma ki_ro_ok_rd : forall segs rlo rhi B (rd : reader) a v,
  arodata_okP segs rlo rhi B rd -> ki_ro_ok segs B a v = true -> rd a = Some v.
Proof.
  intros segs rlo rhi B rd a v HR H. unfold ki_ro_ok in H.
  apply andb_prop in H as [H Hv]. apply andb_prop in H as [H He]. apply andb_prop in H as [Hs Ho].
  apply existsb_exists in Hs as (s & Hin & Hs).
  apply andb_prop in Hs as [Hs Hhi]. apply andb_prop in Hs as [Hw Hlo].
  apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  rewrite (HR a).
  - destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [|discriminate Hv].
    apply Z.eqb_eq in Hv. cbn [option_map]. rewrite Hv. reflexivity.
  - left. exists s. split; [exact Hin|]. split; [exact Hw | lia].
  - intros HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
    apply negb_true_iff in Ho.
    assert (Hx : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static B) = true)
      by (apply existsb_exists; exists r; split; [exact Hr|];
          apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Hx in Ho. discriminate.
  - intros Hx. apply negb_true_iff in He.
    assert (Ht : ((as_errno B <=? a) && (a <? as_errno B + 4))%bool = true)
      by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Ht in He. discriminate.
Qed.

Lemma ki_words_rd : forall segs rlo rhi B (rd : reader) a w ws,
  arodata_okP segs rlo rhi B rd -> ki_words_ok segs B a w ws = true ->
  forall i k, (i < length ws)%nat -> (k < w)%nat ->
  rd (a + Z.of_nat w * Z.of_nat i + Z.of_nat k) = Some (le_byte (nth i ws 0) w k).
Proof.
  intros segs rlo rhi B rd a w ws HR H i k Hi Hk. unfold ki_words_ok in H.
  rewrite forallb_forall in H. specialize (H i ltac:(apply in_seq; lia)).
  rewrite forallb_forall in H. specialize (H k ltac:(apply in_seq; lia)).
  exact (ki_ro_ok_rd segs rlo rhi B rd _ _ HR H).
Qed.

(* bytes the reader gives are the restricted memory's: the val_mem a region's chunk needs *)
Lemma ki_val_mem : forall segs H (m : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> aview segs H m (a + Z.of_nat k) = Some (le_byte v n k)) ->
  val_mem segs (mrestrict H m) a n v.
Proof.
  intros segs H m a n v Hk k Hlt. specialize (Hk k Hlt). unfold aview in Hk.
  destruct (mbyte segs (mrestrict H m) (a + Z.of_nat k)) as [b|]; [|discriminate Hk].
  cbn [option_map] in Hk. injection Hk as Hb.
  replace b with (Z_to_bv 8 (bv_unsigned b)) by apply Z_to_bv_bv_unsigned.
  rewrite Hb. unfold YO0f.le_byte, YG0f.le_byte. reflexivity.
Qed.

Section k.
Variables (segs : list Segment) (rlo rhi : Z) (B : asyms).
Hypothesis KI : KernImg segs B.
Variables (H : word -> bool) (m : word -> option byte).
Hypothesis HRO : arodata_okP segs rlo rhi B (aview segs H m).

Lemma ki_jt_val_mem : forall i, (i < 8)%nat ->
  val_mem segs (mrestrict H m) (KI_JT + 4 * Z.of_nat i) 4 (nth i ki_jt_words 0).
Proof.
  intros i Hi. apply ki_val_mem. intros k Hk.
  pose proof (ki_words_rd segs rlo rhi B _ KI_JT 4 ki_jt_words HRO (ki_jt segs B KI) i k Hi Hk) as R.
  replace (KI_JT + 4 * Z.of_nat i + Z.of_nat k) with (KI_JT + Z.of_nat 4 * Z.of_nat i + Z.of_nat k) by lia.
  exact R.
Qed.

Lemma ki_m_val_mem : forall a v, ki_words_ok segs B a 8 [v] = true ->
  val_mem segs (mrestrict H m) a 8 v.
Proof.
  intros a v Hw. apply ki_val_mem. intros k Hk.
  pose proof (ki_words_rd segs rlo rhi B _ a 8 [v] HRO Hw 0 k ltac:(cbn; lia) Hk) as R.
  cbn [nth] in R. replace (a + Z.of_nat 8 * Z.of_nat 0 + Z.of_nat k) with (a + Z.of_nat k) in R by lia.
  exact R.
Qed.

Lemma ki_m6_val_mem : val_mem segs (mrestrict H m) KI_M6 8 KI_M6_V.
Proof. exact (ki_m_val_mem _ _ (ki_m6 segs B KI)). Qed.
Lemma ki_m5_val_mem : val_mem segs (mrestrict H m) KI_M5 8 KI_M5_V.
Proof. exact (ki_m_val_mem _ _ (ki_m5 segs B KI)). Qed.
Lemma ki_m11_val_mem : val_mem segs (mrestrict H m) KI_M11 8 KI_M11_V.
Proof. exact (ki_m_val_mem _ _ (ki_m11 segs B KI)). Qed.

(* the texts table's words, at a memory whose read-only view is the image's (relro: rlo, rhi = PcapRelro.v's) *)
Lemma ki_tx_val_mem : forall i, (i < 11)%nat -> rlo = PCAP_RLO -> rhi = PCAP_RHI ->
  val_mem segs (mrestrict H m) (KI_TX + 8 * Z.of_nat i) 8 (nth i ki_tx_words 0).
Proof.
  intros i Hi E1 E2. subst rlo rhi. apply ki_val_mem. intros k Hk.
  pose proof (ki_tx segs B KI) as Ht. unfold ki_rwords_ok in Ht.
  rewrite forallb_forall in Ht. specialize (Ht i ltac:(apply in_seq; cbn; lia)).
  rewrite forallb_forall in Ht. specialize (Ht k ltac:(apply in_seq; lia)).
  unfold ki_rel_ok in Ht.
  apply andb_prop in Ht as [Ht Hv]. apply andb_prop in Ht as [Ht He]. apply andb_prop in Ht as [Ht Ho].
  apply andb_prop in Ht as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  replace (KI_TX + 8 * Z.of_nat i + Z.of_nat k) with (KI_TX + Z.of_nat 8 * Z.of_nat i + Z.of_nat k) by lia.
  rewrite (HRO (KI_TX + Z.of_nat 8 * Z.of_nat i + Z.of_nat k)).
  - destruct (seg_rom segs (Z_to_bv 64 _)) as [b|]; [|discriminate Hv].
    apply Z.eqb_eq in Hv. cbn [option_map]. rewrite Hv. reflexivity.
  - right. unfold PCAP_RLO, PCAP_RHI. lia.
  - intros HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
    apply negb_true_iff in Ho.
    assert (Hx : existsb (fun r => (fst r <=? KI_TX + Z.of_nat 8 * Z.of_nat i + Z.of_nat k) &&
                   (KI_TX + Z.of_nat 8 * Z.of_nat i + Z.of_nat k <? fst r + snd r)) (as_owned_static B) = true)
      by (apply existsb_exists; exists r; split; [exact Hr|];
          apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Hx in Ho. discriminate.
  - intros Hx. apply negb_true_iff in He.
    assert (Ht' : ((as_errno B <=? KI_TX + Z.of_nat 8 * Z.of_nat i + Z.of_nat k) &&
                   (KI_TX + Z.of_nat 8 * Z.of_nat i + Z.of_nat k <? as_errno B + 4))%bool = true)
      by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Ht' in He. discriminate.
Qed.

(* the strings' bytes and NULs *)
Lemma ki_str_rd : forall p bs, In (p, bs) ki_strs -> forall i, (i < length bs)%nat ->
  aview segs H m (p + Z.of_nat i) = Some (nth i bs 0).
Proof.
  intros p bs Hin i Hi. pose proof (ki_str segs B KI) as Hs. unfold ki_strs_ok in Hs.
  rewrite forallb_forall in Hs. specialize (Hs (p, bs) Hin). cbn [fst snd] in Hs.
  rewrite forallb_forall in Hs. specialize (Hs i ltac:(apply in_seq; lia)).
  exact (ki_ro_ok_rd segs rlo rhi B _ _ _ HRO Hs).
Qed.
End k.

(* every image byte is visible at every memory: mbyte falls back to seg_rom, which ki_rom says is defined there *)
Lemma ki_vis : forall segs B, KernImg segs B -> forall H (m : word -> option byte) a,
  0x10000 <= a < pcap_img_end -> aview segs H m a <> None.
Proof.
  intros segs B KI H m a Ha Hn. pose proof (ki_rom segs B KI a Ha) as Hr.
  unfold aview in Hn. destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; [cbn in Hn; discriminate Hn|].
  unfold mbyte in Eb. destruct (mrestrict H m (Z_to_bv 64 a)); [discriminate Eb | exact (Hr Eb)].
Qed.

End a.
