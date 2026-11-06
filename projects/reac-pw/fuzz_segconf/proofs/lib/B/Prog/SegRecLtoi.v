(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3, unstripped twin 80e82127e8ca): the
   three listing facts that lib/B/Prog/SegProgClosed.v keeps as the Section hypotheses h_mcrom, h_pgs and h_pg_ptr,
   as lemmas over the allocator record B with image B's symbol record (YF0m.SegBSyms B). Each statement is the
   hypothesis's text at the close's terms (tfibsegs, SegInstB's addresses), under the close's Require Import lines,
   so that `seg_mcrom B HB`, `seg_pgs B HB` and `seg_pg_ptr` discharge them.
   - seg_mcrom (m_file: musl memchr's word-constant window [memchr_loA, memchr_hiA) = [0x10350, 0x10370)): read-only
     image bytes by the record's image facts (SegRecImg.seg_img_facts_tfib, field cif_snl_rom), outside the record's
     owned statics and the errno cell by SegRecBase.seg_snl_unowned.
   - seg_pgs (LLVMFuzzerTestOneInput's longl, ltoi_PG longlA = [(0x5dee40, 0x5dee40 + 121)]): the record's one program
     static (YF0m's ts_prog: as_prog_static B = TFIB_PROG_STATIC = [(0x5dee40, 121)]), and in the image by the
     record's image facts (cif_prog_img over SegGlob.seg_PG, which is ltoi_PG longlA by conversion).
   - seg_pg_ptr (LLVMFuzzerTestOneInput: the first word of each of m_key.words' 5 entries at wordsA = 0xa2040 and of
     the 11 rows of fuzz_catalogue at catA = 0xa20a0, row stride pin_spec.CAT_ROW = 0x128): each is a pointer into
     .rodata (0x102e0 .. 0x23a6c), 64 KiB and more below longl. The 16 words, read from the twin's PT_LOAD bytes
     (ET_EXEC: the file holds the final values) and checked against the image's ROM bytes by pg_ptr_rd:
       words[0..4]  0xa2040 0x21140  0xa2048 0x21160  0xa2050 0x21180  0xa2058 0x211a0  0xa2060 0x211c0
       rows[0..10]  0xa20a0 0x21d40  0xa21c8 0x21da0  0xa22f0 0x21e00  0xa2418 0x21e60  0xa2540 0x21ec0
                    0xa2668 0x21f20  0xa2790 0x21f80  0xa28b8 0x21fe0  0xa29e0 0x22040  0xa2b08 0x220a0
                    0xa2c30 0x22100
     The largest, 0x22100, plus 65536 is 0x32100 <= longlA = 0x5dee40. The image is read once (pg_ptr_rd, the 16
     words by vm_compute); the bound is a check over those 16 numbers (pg_ptr_words_below).
   proves no function (kind: listing facts over image B's bytes and the allocator record's symbol record). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d YCbq YC5d YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable SegSyms SegList SegPa SegPaLib PaLibF SegObj SegGlob SegImg SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecBase SegRecImg m_file_memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require LLVMFuzzerTestOneInput_c.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- h_mcrom: musl memchr's word-constant window ---------------------------------------------------------- *)
Lemma seg_mcrom : forall B, YF0m.SegBSyms B -> m_file_memchr.memchr_rom_fact tfibsegs B.
Proof.
intros B HB a Ha. split.
- exact (SegRecBase.cif_snl_rom _ _ (SegRecImg.seg_img_facts_tfib B HB) a Ha).
- exact (SegRecBase.seg_snl_unowned B HB a Ha).
Qed.

(* ---- h_pgs: longl is the record's program static and in the image ------------------------------------------ *)
Lemma seg_pgs : forall B, YF0m.SegBSyms B -> forall a, YI04.inFP (LLVMFuzzerTestOneInput_c.ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img tfibsegs a.
Proof.
intros B HB a Ha. split.
- rewrite (YF0m.ts_prog B HB). unfold YF0m.TFIB_PROG_STATIC.
  destruct Ha as (r & Hr & Hra). unfold LLVMFuzzerTestOneInput_c.ltoi_PG in Hr.
  destruct Hr as [<- | []]. cbn [fst snd] in Hra. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
  unfold longlA, A_LONGL, LLVMFuzzerTestOneInput_c.LONGL_N in Hra. lia.
- exact (SegRecBase.cif_prog_img _ _ (SegRecImg.seg_img_facts_tfib B HB) a Ha).
Qed.

(* ---- h_pg_ptr: the first words of m_key.words and of the catalogue rows lie 64 KiB below longl -------------- *)
(* the 16 addresses: m_key.words' 5 entries, then the catalogue's 11 rows *)
Definition pg_ptr_addrs : list Z :=
List.map (fun i => wordsA + 8 * Z.of_nat i) (List.seq 0 5) ++
List.map (fun i => pin_spec.row_addr catA i) (List.seq 0 pin_spec.CAT_N).
(* the close's reader: the image's ROM byte *)
Definition pg_rd (x : Z) : option Z :=
option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 x)).
(* the 16 words at those addresses, in that order (measured on the twin; the header) *)
Definition pg_ptr_words : list Z :=
[0x21140; 0x21160; 0x21180; 0x211a0; 0x211c0;
 0x21d40; 0x21da0; 0x21e00; 0x21e60; 0x21ec0; 0x21f20; 0x21f80; 0x21fe0; 0x22040; 0x220a0; 0x22100].
(* the image read, once *)
Lemma pg_ptr_rd : List.map (rdword pg_rd) pg_ptr_addrs = List.map Some pg_ptr_words.
Proof. vm_compute. reflexivity. Qed.
Lemma pg_ptr_words_below : List.forallb (fun p => p + 65536 <=? longlA) pg_ptr_words = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_pg_ptr : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Proof.
intros a p Ha Hp. change (rdword pg_rd a = Some p) in Hp.
assert (Hin : In a pg_ptr_addrs).
{ unfold pg_ptr_addrs. apply in_or_app.
  destruct Ha as [(i & Hi & ->) | (i & Hi & ->)]; [left | right];
    apply in_map_iff; exists i; (split; [reflexivity | apply in_seq; lia]). }
assert (Hw : In (Some p) (List.map Some pg_ptr_words)).
{ rewrite <- pg_ptr_rd, <- Hp. exact (in_map (rdword pg_rd) _ _ Hin). }
apply in_map_iff in Hw as (q & Hq & Hqin). injection Hq as Hqp. subst q.
pose proof (proj1 (forallb_forall _ _) pg_ptr_words_below p Hqin) as H. cbv beta in H.
apply Z.leb_le in H. exact H.
Qed.

Print Assumptions seg_mcrom.
Print Assumptions seg_pgs.
Print Assumptions seg_pg_ptr.
