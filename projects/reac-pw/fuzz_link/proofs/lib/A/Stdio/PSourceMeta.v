(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ASan meta-region invariant and the image laws for libreac/fuzz_pcap's
   READ stream, stated over PSource.v's asource_syms.

   WHY THIS FILE EXISTS. The core states the meta invariant (ameta_ok, YE00.v:110; ameta_inv,
   YE01.v:137) and the image laws that make it usable (asink_img_laws, YE01.v:25) over cgif's
   SINK record asink_syms, because cgif's harness writes a file. pcap's harness READS a memory
   stream and has no sink: no path, no write trailer. a Theorem Labs lane (21:20Z) found that PFclose.v's
   `ameta_inv` premise therefore had no definition over asource_syms. The two options were to
   drop it or define it; it is DEFINED here, because it cannot be dropped:
     - the donor's fclose proof consumes it (cgif lib/A/AE24.v:122 via ameta_ptr_of_AR), and the
       donor preserves it across the call (ameta_inv_kept, YE01.v:151) for 20+ consumer files;
     - the meta region is where the allocator keeps the state free() updates, so fclose's two
       frees cannot be walked without it.
   Carrying a whole asink_syms just for its two meta fields would be worse than either: the
   caller would have to discharge SINK image laws (path, trailer, the sink environment) for a
   program that has no sink.

   WHAT IS COPIED AND WHAT IS NOT. The bodies below are the donor's, field for field, with
   ak_* -> as_* (PSource.v:87-101 already carries as_meta_ptr / as_meta_mem / as_can_got /
   as_icells, mirroring asink_syms). The stdio environment's cells are pcap's, not cgif's:
     threaded, need_locks, ofl_lock (+16, lock and head, as the donor's aenv_addr), the
     "rb\0" mode literal (as_mode, 3 bytes), musl's "rwa\0" mode-set literal (as_rwa, 4 bytes --
     the donor's ak_rwa; a field of the record, not a named constant), and the canary (8 bytes).
   No path and no trailer, because pcap has neither.

   THE DONOR'S TWO LEMMAS over these definitions are PORTED below (Section L), from YE01.v:139-169
   (ameta_ptr_of_AR, ameta_inv_kept) with ak_* -> as_*, AIL -> ASIL, ail_* -> asil_*, ameta_inv ->
   asrc_meta_inv. They are invariant lemmas over definitions, ported from a released proof: no
   function is proved here.

   AMETA_SIZE (3727360, YE00.v:21) is MEASURED on pcap's image, not only cgif's constant
   (a Theorem Labs lane, 21:50Z): the metadata map is 31051 buckets x 120 B = 3726120, page-rounded by
   MmapOrDie to 0x38E000 = 3727360 (InitializeAsanInterceptors+0x4c, string "AddrHashMap"). The
   same measurement gives this record's two meta cells for the concrete instance:
   as_meta_ptr = interceptor_metadata_map 0xa9c80, as_meta_mem = metadata_mem 0xa9c88. (An
   earlier version of this header called it unmeasured; that was true when written, and is not
   now.) AOFL_HEAD is YI16.sk_ofl_head from the per-image sink_head instance
   (YCbq.v:84), not a cgif literal; PSource.v's asource_head_law ties it to as_ofl_head K, and
   pcap's measured value is 0x652308.

   IMAGE ROOT: the ORIGINAL v1.9.0 set (see PSource.v's header). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YE00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq.
(* YE01 for mbyte_kept_of_aview, YM05 for RunCeil: both used by the ported lemmas in Section L. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Stdio Require Import PSource.
Import ListNotations.
Open Scope Z_scope.

(* The stdio environment's cells, as an address set: the source analogue of YE00.v's aenv_addr.
   Exactly the cells asrc_stdio_env (PSource.v) pins, at the widths it pins them, except that the
   ofl_lock range is +16 as the donor's is (lock word and the open-file list head above it). *)
Definition asrc_env_addr (K : asource_syms) (a : Z) : Prop :=
  a = as_threaded K \/ a = as_need_locks K \/ (as_ofl_lock K <= a < as_ofl_lock K + 16) \/
  (as_mode K <= a < as_mode K + 3) \/ (as_rwa K <= a < as_rwa K + 4) \/
  (as_canary K <= a < as_canary K + 8).

(* The image laws for the read stream: the source analogue of asink_img_laws (YE01.v:25), clause
   for clause. Discharged ONCE, at instantiation with pcap's measured addresses, by whoever builds
   the concrete asource_syms -- not per walk.
   SK is an EXPLICIT parameter (a Theorem Labs lane, 21:58Z), unlike the donor's {SK}: it fixes
   AOFL_HEAD, and lib/Reusable/YI5b.v:12 declares a #[global] instance for the PLAIN image's head, so
   an implicit SK could be filled silently with the wrong head by any consumer whose closure reaches
   YI5b. The caller must name the ASan image's head. *)
Record asource_img_laws (SK : YI16.sink_head) (segs : list Segment) (B : asyms) (K : asource_syms)
  : Prop := mkASIL {
  asil_head : as_ofl_head K = AOFL_HEAD;
  asil_env : forall a, asrc_env_addr K a ->
    in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
  asil_env_off : forall a, asrc_env_addr K a ->
    AOFL_HEAD <= a < AOFL_HEAD + 8 \/ ~ (AOFL_HEAD <= a < AOFL_HEAD + 8);
  asil_env_static : forall a,
    a = as_threaded K \/ a = as_need_locks K \/ (as_ofl_lock K <= a < as_ofl_lock K + 4) \/
    (as_mode K <= a < as_mode K + 3) \/ (as_rwa K <= a < as_rwa K + 4) \/
    (as_canary K <= a < as_canary K + 8) -> ~ (AOFL_HEAD <= a < AOFL_HEAD + 8);
  asil_can_got : forall ly, In (z8 (ANum (as_can_got K)) (as_canary K)) (as_const B ly);
  asil_meta : forall a, as_meta_mem K <= a < as_meta_mem K + 8 ->
    in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
    a < AOFL_HEAD;
  asil_meta_ptr : forall ly, In (z8 (ANum (as_meta_ptr K)) (as_meta_mem K)) (as_const B ly);
  asil_errno_img : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a;
  asil_icells : forall ly c, In c (as_icells K) -> In (z8 (ANum (fst c)) (snd c)) (as_const B ly)
}.

Section M.
Variable segs : list Segment.
Variable K : asource_syms.

(* The meta region: the source analogue of YE00.v:110 ameta_ok, body identical with ak_ -> as_. *)
Definition asrc_meta_ok (m : word -> option byte) (M : Z) : Prop :=
  val_mem segs m (as_meta_ptr K) 8 (as_meta_mem K) /\
  val_mem segs m (as_meta_mem K) 8 M /\
  0 <= M /\ M + AMETA_SIZE <= 2 ^ 47 /\ M mod 4096 = 0 /\
  (forall a, M <= a < M + AMETA_SIZE -> mbyte segs m a = Some (Z_to_bv 8 0)).

(* The source analogue of YE01.v:137 ameta_inv, body identical. *)
Definition asrc_meta_inv (ly : alayout) (m : word -> option byte) (M : Z) : Prop :=
  In (M, AMETA_SIZE) (ly_extra ly) /\ (forall a, in_img segs a -> a < M) /\ asrc_meta_ok m M.

End M.

(* ---------------------------------------------------------------------------------------------- *)
(* The donor's meta lemmas, PORTED from YE01.v:139-169 with the renaming in the header. The proofs  *)
(* are the donor's line for line: the journal (ajournal), the allocator relation (AR) and the       *)
(* helpers (am_const, fp_spares_below, AR_extra_law_ok, val_mem_frame, mbyte_kept_of_aview) are the  *)
(* same core objects; only the symbol record and its laws record change. One mechanical difference: *)
(* SK is an explicit parameter of asource_img_laws, so each asil_* projection takes one more `_`     *)
(* than the donor's ail_* (asil_meta_ptr _ _ _ _ ASIL, not ail_meta_ptr _ _ _ AIL).                  *)
(* ---------------------------------------------------------------------------------------------- *)
Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Hypothesis ASIL : asource_img_laws SK segs B K.
Local Notation ajournal := (ajournal segs B).
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* YE01.v:139 ameta_ptr_of_AR *)
Lemma asrc_meta_ptr_of_AR : forall ly S W mem md,
AR segs B ly S W mem md -> val_mem segs (rd W mem) (as_meta_ptr K) 8 (as_meta_mem K).
Proof.
intros ly S W mem md HAR k Hk.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
pose proof (proj1 (Forall_forall _ _) HC _ (asil_meta_ptr _ _ _ _ ASIL ly)) as Hc. unfold z8, c8, cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte segs (mrestrict (w_H W) mem) (as_meta_ptr K + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte (as_meta_mem K) 8 k) with (YG0f.le_byte (as_meta_mem K) 8 k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.

(* YE01.v:151 ameta_inv_kept *)
Lemma asrc_meta_inv_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
asrc_meta_inv segs K ly (rd W mem) M -> asrc_meta_inv segs K ly' (rd W' mem') M.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M HJ (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ).
pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (HX' : In (M, AMETA_SIZE) (ly_extra ly')) by (rewrite Eextra; exact HX).
split; [exact HX'|]. split; [exact Himg|]. split; [exact (asrc_meta_ptr_of_AR _ _ _ _ _ HAR')|]. split.
- eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply mbyte_kept_of_aview.
destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt). apply (F3 x Hi Hns He). apply fp_spares_below. exact Hlt.
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
intros a Ha. rewrite <- (HZ a Ha). apply mbyte_kept_of_aview. apply F5.
+ apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
+ intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi.
destruct (AR_extra_law_ok segs B ly' S' W' mem' md' a HAR'
ltac:(apply Exists_exists; exists (M, AMETA_SIZE); split; [exact HX' | unfold in_zr; cbn [fst snd]; lia])) as (_ & _ & _ & _ & Hni & _).
exact (Hni Hi).
Qed.

End L.

(* GUARD (a Theorem Labs lane, 21:58Z): SK must stay an EXPLICIT argument of every object here that
   takes it. Each Check passes SK by position. If SK ever went back to implicit ({SK}), Coq would fill
   it by instance search and the positional SK would land on the segs argument, so this file would
   stop compiling. *)
Check (fun (SK : YI16.sink_head) (segs : list Segment) (B : asyms) (K : asource_syms) =>
  asource_img_laws SK segs B K).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => asrc_meta_ptr_of_AR (rc:=rc) SK).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => asrc_meta_inv_kept (rc:=rc) SK).
