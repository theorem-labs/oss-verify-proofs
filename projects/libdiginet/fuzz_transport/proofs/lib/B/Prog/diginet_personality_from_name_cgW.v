(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_codec proofs/libdiginet/fuzz_codec/lib/Prog/diginet_personality_from_name.v at d8e4e696562a3ec070d61f99e264ce9d80f5a5bd to fuzz_transport's images *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Prog/diginet_personality_from_name.v, with its module paths and module names changed; 968 of its 996 lines of code are new or changed and 111 lines of the source are left out. *)
(* diginet_personality_from_name_cgW: Theorem transport_diginet_personality_from_name_cg_holds : the statement
   transport_diginet_personality_from_name_cg_holds_stmt of lib/B/Prog/diginet_personality_from_name_cg.v, the machine
   walk of diginet_personality_from_name (src/diginet_codec.c:17-25) on fuzz_transport.asan-ubsan at 0x8c050 =
   transportb_sigma TB_diginet_personality_from_name (172 bytes, frame 48), in decode's caller-journal form. It is the
   port of image A's walk lib/A/Prog/diginet_personality_from_name_cgW.v (same lemma names, here in image B's
   namespace): the code is the same 43 instructions with image B's immediates, and image B's code has no UBSan trap.

   The walk (the shape of decode's lib/A/Prog/check_refusal_cg_walk.v):
   - an INNER journal is started at the entry (lib/Reusable/YCbq.v ajournal_sub_init; window
     [spZ regs - PFROM_STK, spZ regs), no footprint, no frame of its own);
   - the code runs as three footprint runs (lib/Lib/ExecF.v evtF, carried into SRr by lib/B/Prog/TransportFevt.v
     decode_run):
       pfw_run1_F  0x8c050 .. the call at 0x8c0b8: the frame (ra, s0 .. s4 saved), `beqz a0` not taken (x <> 0),
                   s1 = the shadow base through GOT_CELL_K (0xa3cf0) / CELL_K (0xac678), s3 = personalities
                   (0xa3b00), the turn k = 0: the instrumented check of the 8-byte load at personalities + 8 (its
                   shadow byte is 0: transport_cells' zero-shadow row of personalities), a1 = TRANS_PNAME0, a0 = x;
       pfw_run2_F  the return 0x8c0bc of the first call: a0 = 0 returns personalities (the epilogue reloads the
                   frame); else `bnez` goes back to the loop head and the turn k = 1 reaches the call again with
                   a1 = TRANS_PNAME1;
       pfw_run3_F  the return of the second call: a1 = .. & (1 ^ 1) = 0, a0 = personalities + 24 when the result is
                   0, else 0; the epilogue and `ret` (0x8c0f4).
     The error path 0x8c0f8 (__asan_report_load8) is not reached: the shadow byte of each checked load is 0.
   - each call of the strcmp wrapper (the trampoline 0x42d28) is the statement's named hypothesis astrcmp_realizes,
     read on the inner journal by pfw_strcmp_cstr_at: the C string of tb at x against the 9-byte name (CNTRL|24 /
     MAINUNIT and its 0); a0 = the sign of C strcmp (pfw_strcmpZ), 0 exactly when the strings are equal;
   - the inner journal composes with the caller's (YCbq.v ajournal_sub), the kept bytes come from YCbq.v
     acall_kept_of_journal, no event, no meter charge (pfw_close).
   The string's ranges come from the kit (DgnTransportBCg.v trans_src_ok_rd, trans_rd_ok_sub, trans_rd_ok_view), the
   names' shadow from transport_cells and trans_pfrom_cells (image B: each name has its own group of 8 shadow bytes,
   pfw_name_sh), their bytes from trans_rom_view_rd.

   Copied and adapted (provenance): the image-generic lemmas (pfw_cs_k .. pfw_strcmpZ_unsigned, pfw_split ..
   pfw_res, pfw_cstr_at .. pfw_cstr_rom, pfw_bytes_view .. pfw_sltu0, pfw_strcmp_cstr_at, pfw_pres_groups,
   pfw_close) are image A's lib/A/Prog/diginet_personality_from_name_cgW.v (origin/cold/h-disco-16-aw29
   c8f7666ff568), copied rather than Required so that no image-A kit file enters this file's closure; they are in
   turn adapted from origin/cold/h-dgn-c1-ai 879253f2304d proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalkStr.v:45-354
   (cw_cs_k .. cw_strcmp_cstr_at) and diginet_personality_from_name_A.v (pfn_res), and from
   lib/Prog/diginet_personality_from_name.v (pfn_split / pfn_cstring). pfw_aview_vis / pfw_aview_some are image A's
   lib/A/Prog/DgnTransportCgRun.v decode_aview_vis / decode_aview_some at image B's segments. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require codec_cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportFevt LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module YKW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module PCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module DSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module CCW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.codec_cells.

(* ================================ the addresses ================================ *)
Definition PFW_ENTRY : Z := transportb_sigma TB_diginet_personality_from_name.
Definition PFW_STRCMP : Z := transportb_sigma TB___interceptor_trampoline_strcmp.
(* the return address of the call at 0x8c0b8 *)
Definition PFW_RET : Z := PFW_ENTRY + 0x6c.
(* the name personalities[k].announce_name points to *)
Definition PFW_NAME (k : Z) : Z := if k =? 0 then TRANS_PNAME0 else TRANS_PNAME1.

Ltac pfw_lits :=
  unfold PFW_RET, PFW_NAME, TRANS_PERS, TRANS_PNAME0, TRANS_PNAME1 in *;
  repeat match goal with
  | |- context [PFW_ENTRY] => let v := eval vm_compute in PFW_ENTRY in change PFW_ENTRY with v
  | H : context [PFW_ENTRY] |- _ => let v := eval vm_compute in PFW_ENTRY in change PFW_ENTRY with v in H
  | |- context [PFW_STRCMP] => let v := eval vm_compute in PFW_STRCMP in change PFW_STRCMP with v
  | H : context [PFW_STRCMP] |- _ => let v := eval vm_compute in PFW_STRCMP in change PFW_STRCMP with v in H
  end.

(* ================================ C strings over list Z ================================ *)
(* the index where the C strings x and y (no 0 in either) first differ, or where both end *)
Fixpoint pfw_cs_k (x y : list Z) : nat :=
  match x, y with
  | a :: x', b :: y' => if a =? b then S (pfw_cs_k x' y') else O
  | _, _ => O
  end.
Lemma pfw_cs_k_le : forall x y, (pfw_cs_k x y <= length x)%nat /\ (pfw_cs_k x y <= length y)%nat.
Proof.
  induction x as [|a x IH]; intros [|b y]; cbn [pfw_cs_k length]; try lia.
  destruct (a =? b); [destruct (IH y); lia | lia].
Qed.
Lemma pfw_cs_k_spec : forall x y, ~ In 0 x -> ~ In 0 y ->
  (forall j, (j < pfw_cs_k x y)%nat -> nth j (x ++ [0]) 0 = nth j (y ++ [0]) 0 /\ nth j (x ++ [0]) 0 <> 0) /\
  (nth (pfw_cs_k x y) (x ++ [0]) 0 <> nth (pfw_cs_k x y) (y ++ [0]) 0 \/ nth (pfw_cs_k x y) (x ++ [0]) 0 = 0) /\
  (nth (pfw_cs_k x y) (x ++ [0]) 0 = nth (pfw_cs_k x y) (y ++ [0]) 0 <-> x = y).
Proof.
  induction x as [|a x IH]; intros [|b y] Nx Ny; cbn [pfw_cs_k app nth].
  - split; [intros j Hj; lia|]. split; [right; reflexivity|]. split; intros; reflexivity.
  - split; [intros j Hj; lia|]. split; [right; reflexivity|].
    split; [intros H; exfalso; apply Ny; left; symmetry; exact H | discriminate].
  - split; [intros j Hj; lia|]. split; [left; intros H; apply Nx; left; exact H|].
    split; [intros H; exfalso; apply Nx; left; exact H | discriminate].
  - destruct (Z.eqb_spec a b) as [Eab|Nab]; cbv beta iota.
    + subst b. destruct (IH y) as (P1 & P2 & P3); [intros H; apply Nx; right; exact H | intros H; apply Ny; right; exact H |].
      split; [intros [|j] Hj; cbn [nth]; [split; [reflexivity | intros H; apply Nx; left; exact H] | apply P1; lia]|].
      cbn [nth]. split; [exact P2|].
      rewrite P3. split; [intros ->; reflexivity | intros H; injection H; auto].
    + split; [intros j Hj; lia|]. cbn [nth]. split; [left; exact Nab|].
      split; [intros H; exfalso; exact (Nab H) | intros H; injection H as H _; exfalso; exact (Nab H)].
Qed.
(* the wrapper's value at that index: the sign of C strcmp(x, y) *)
Definition pfw_strcmpZ (x y : list Z) : Z :=
  strcmp_res (nth (pfw_cs_k x y) (x ++ [0]) 0) (nth (pfw_cs_k x y) (y ++ [0]) 0).
Lemma pfw_strcmp_res_cases : forall c1 c2,
  strcmp_res c1 c2 = 0 \/ strcmp_res c1 c2 = -1 \/ strcmp_res c1 c2 = 1.
Proof. intros c1 c2. unfold strcmp_res. destruct (c1 =? c2); [auto|]. destruct (c1 <? c2); auto. Qed.
Lemma pfw_strcmpZ_0 : forall x y, ~ In 0 x -> ~ In 0 y -> (pfw_strcmpZ x y = 0 <-> x = y).
Proof.
  intros x y Nx Ny. destruct (pfw_cs_k_spec x y Nx Ny) as (_ & _ & P3). rewrite <- P3. unfold pfw_strcmpZ, strcmp_res.
  destruct (Z.eqb_spec (nth (pfw_cs_k x y) (x ++ [0]) 0) (nth (pfw_cs_k x y) (y ++ [0]) 0)) as [E|E]; [tauto|].
  destruct (_ <? _); split; intros H; first [discriminate H | contradiction].
Qed.
(* a0 after the call reads 0 exactly when the strings are equal *)
Lemma pfw_strcmpZ_unsigned : forall x y, ~ In 0 x -> ~ In 0 y ->
  (bv_unsigned (w64 (pfw_strcmpZ x y)) = 0 <-> x = y).
Proof.
  intros x y Nx Ny. rewrite <- (pfw_strcmpZ_0 x y Nx Ny).
  destruct (pfw_strcmp_res_cases (nth (pfw_cs_k x y) (x ++ [0]) 0) (nth (pfw_cs_k x y) (y ++ [0]) 0)) as [E|[E|E]];
  unfold pfw_strcmpZ; rewrite E; split; intros H; first [reflexivity | vm_compute in H; discriminate H | discriminate H].
Qed.

(* ================================ the bytes of tb ================================ *)
(* a byte list holding a 0 is the bytes before its first 0, that 0, and the rest *)
Lemma pfw_split : forall tb : list byte, In (DSW.b8 0) tb ->
  exists sx rest, tb = sx ++ DSW.b8 0 :: rest /\ ~ In (DSW.b8 0) sx.
Proof.
  induction tb as [|b tb IH]; intros H; [destruct H|].
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E].
  - exists [], tb. split; [|intros []]. cbn [app]. f_equal. apply bv_eq. rewrite E. reflexivity.
  - destruct H as [H|H]; [subst b; exfalso; apply E; reflexivity|].
    destruct (IH H) as (sx & rest & -> & N). exists (b :: sx), rest. split; [reflexivity|].
    intros [H'|H']; [subst b; apply E; reflexivity | exact (N H')].
Qed.
Lemma pfw_nz : forall sx : list byte, ~ In (DSW.b8 0) sx -> ~ In 0 (map DSW.bz sx).
Proof.
  intros sx N H. apply in_map_iff in H as (b & Hb & Hin). apply N.
  replace (DSW.b8 0) with b; [exact Hin|]. apply bv_eq. unfold DSW.bz in Hb. rewrite Hb. reflexivity.
Qed.
Lemma pfw_cstring_app : forall s rest, ~ In 0 s -> CCW.cstring (s ++ 0 :: rest) = s.
Proof.
  induction s as [|a s IH]; intros rest N; cbn [app CCW.cstring]; [reflexivity|].
  destruct (Z.eqb_spec a 0) as [E|E]; [exfalso; apply N; left; exact E|].
  f_equal. apply IH. intros H. apply N. right. exact H.
Qed.
Lemma pfw_len_c24 : length CCW.NAME_C24 = 8%nat.
Proof. reflexivity. Qed.
Lemma pfw_len_pc : length CCW.NAME_PC = 8%nat.
Proof. reflexivity. Qed.
(* the result on the C string of tb *)
Lemma pfw_res : forall tb sx rest, tb = sx ++ DSW.b8 0 :: rest -> ~ In 0 (map DSW.bz sx) ->
  trans_pfrom_res tb =
  if list_eq_dec Z.eq_dec (map DSW.bz sx) CCW.NAME_C24 then TRANS_PERS
  else if list_eq_dec Z.eq_dec (map DSW.bz sx) CCW.NAME_PC then TRANS_PERS + 24 else 0.
Proof.
  intros tb sx rest -> N. unfold trans_pfrom_res.
  change (CCW.zb (sx ++ DSW.b8 0 :: rest)) with (map DSW.bz (sx ++ DSW.b8 0 :: rest)).
  rewrite map_app. cbn [map]. change (DSW.bz (DSW.b8 0)) with 0. rewrite (pfw_cstring_app _ _ N). reflexivity.
Qed.

(* ================================ a C string in memory ================================ *)
Lemma pfw_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small v (2 ^ 8)) by (change (2 ^ 8) with 256; lia). apply Z.mod_small. lia.
Qed.
Definition pfw_cstr_at (W : world tfibsegs) (m : word -> option byte) (x : Z) (s : list Z) : Prop :=
  ~ In 0 s /\
  forall j, (j <= length s)%nat -> aview tfibsegs (w_H W) m (x + Z.of_nat j) = Some (nth j (s ++ [0]) 0).
Lemma pfw_cstr_of_garr8 : forall (W : world tfibsegs) m x s rest,
  garr8 tfibsegs (mrestrict (w_H W) m) x (s ++ 0 :: rest) -> ~ In 0 s -> pfw_cstr_at W m x s.
Proof.
  intros W m x s rest Hg N. split; [exact N|]. intros j Hj.
  replace (s ++ 0 :: rest) with ((s ++ [0]) ++ rest) in Hg by (rewrite <- app_assoc; reflexivity).
  assert (Hj' : (j < length ((s ++ [0%Z]) ++ rest))%nat) by (rewrite !length_app; cbn [length]; lia).
  destruct (Hg j Hj') as [Hv Hr].
  rewrite app_nth1 in Hv, Hr by (rewrite length_app; cbn [length]; lia).
  specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
  assert (Hb : mbyte tfibsegs (mrestrict (w_H W) m) (x + Z.of_nat j) = Some (Z_to_bv 8 (nth j (s ++ [0]) 0))).
  { rewrite Hv. f_equal. f_equal. apply pfw_le_byte1. exact Hr. }
  unfold aview. rewrite Hb. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hr.
Qed.
Lemma pfw_cstr_kept : forall (W : world tfibsegs) m m' x s lo hi,
  pfw_cstr_at W m x s ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  0 <= x -> x + Z.of_nat (length s) + 1 <= 2 ^ 64 -> (x + Z.of_nat (length s) + 1 <= lo \/ hi <= x) ->
  pfw_cstr_at W m' x s.
Proof.
  intros W m m' x s lo hi (N & A) HK Hx Hxs Hd. split; [exact N|]. intros j Hj.
  rewrite HK; [apply A; exact Hj | lia | lia].
Qed.
Lemma pfw_cstr_rd : forall (W : world tfibsegs) m x s, pfw_cstr_at W m x s ->
  forall a, x <= a < x + Z.of_nat (length s) + 1 -> aview tfibsegs (w_H W) m a <> None.
Proof.
  intros W m x s (_ & A) a Ha. replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia.
  rewrite A by lia. discriminate.
Qed.
(* a C string of the image: the image holds it and its 0 (pfw_img_cstr, by computation) at bytes trans_rom_view_rd
   reads as the image's *)
Definition pfw_img_cstr (x : Z) (s : list Z) : bool :=
  forallb (fun v => negb (v =? 0)) s &&
  forallb (fun j => match YKW.seg_rom tfibsegs (Z_to_bv 64 (x + Z.of_nat j)) with
                    | Some b => bv_unsigned b =? nth j (s ++ [0]) 0
                    | None => false end) (seq 0 (S (length s))).
Lemma pfw_cstr_rom : forall (W : world tfibsegs) m x s,
  trans_rom_view_rd W m -> (forall j, (j <= length s)%nat -> trans_in_ro_rd (x + Z.of_nat j)) ->
  pfw_img_cstr x s = true -> pfw_cstr_at W m x s.
Proof.
  intros W m x s HRO Hin Hc. unfold pfw_img_cstr in Hc. apply andb_prop in Hc as [Hz Hb].
  split.
  - intros H0. pose proof (proj1 (forallb_forall _ _) Hz 0 H0) as H. discriminate H.
  - intros j Hj. rewrite (HRO _ (Hin j Hj)).
    assert (Hk : In j (seq 0 (S (length s)))) by (apply in_seq; lia).
    pose proof (proj1 (forallb_forall _ _) Hb j Hk) as H. cbv beta in H.
    destruct (YKW.seg_rom tfibsegs (Z_to_bv 64 (x + Z.of_nat j))) as [b|]; [|discriminate H].
    apply Z.eqb_eq in H. rewrite <- H. reflexivity.
Qed.
(* a byte the view reads is not hidden, and is the footprint view's byte *)
Lemma pfw_aview_vis : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff tfibsegs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YKW.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.
Lemma pfw_aview_some : forall (W : world tfibsegs) mem a v, aview tfibsegs (w_H W) mem a = Some v ->
  w_H W (Z_to_bv 64 a) = false /\ exists b : byte, mrd rsegs mem (wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros W mem a v H. pose proof (pfw_aview_vis W mem a v H) as Hv. split; [exact Hv|].
  assert (E : aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs mem (wa a)))
    by (unfold aview, YP09.mbyte, mrestrict, mrd, wa; rewrite Hv; reflexivity).
  rewrite E in H.
  destruct (mrd rsegs mem (wa a)) as [b|] eqn:E2; [|discriminate H]. exists b. split; [reflexivity|].
  injection H as H. exact H.
Qed.
(* a byte of a range of TRANS_RO_RD *)
Lemma pfw_ro_rd : forall g gn a, In (g, gn) TRANS_RO_RD -> g <= a < g + gn -> trans_in_ro_rd a.
Proof. intros g gn a Hin Ha. unfold trans_in_ro_rd. apply Exists_exists. exists (g, gn). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia. Qed.
Ltac pfw_in := unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app]; repeat (first [left; reflexivity | right]).
Lemma pfw_ro_vis : forall (W : world tfibsegs) m a, trans_rom_view_rd W m -> trans_in_ro_rd a -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a HR H. destruct (trans_ro_rd_rom_clean a H) as [_ [b Hb]].
  apply (pfw_aview_vis W m a (bv_unsigned b)). rewrite (HR a H), Hb. reflexivity.
Qed.

(* ================================ bytes for the footprint runs ================================ *)
Lemma pfw_bytes_view : forall (W : world tfibsegs) m A bs,
  (forall i, (i < length bs)%nat -> aview tfibsegs (w_H W) m (A + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))) ->
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m A bs.
Proof.
  intros W m A bs HV H0 H1. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (pfw_aview_some W m (A + Z.of_nat i) _ (HV i Hi)) as (_ & b & Hb & Eb).
  rewrite Hb. rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi). f_equal. apply bv_eq. exact Eb.
Qed.
Lemma pfw_bytes1 : forall (W : world tfibsegs) m A,
  aview tfibsegs (w_H W) m A = Some 0 -> 0 <= A < 2 ^ 64 -> bytes_at rsegs m A [Z_to_bv 8 0].
Proof.
  intros W m A HV HA. apply (pfw_bytes_view W m A); [|lia | cbn [length]; lia].
  intros i Hi. cbn [length] in Hi. assert (i = 0%nat) as -> by lia. rewrite Z.add_0_r. exact HV.
Qed.
Definition pfw_img_bytes (A : Z) (bs : list byte) : bool :=
  forallb (fun i => match YKW.seg_rom tfibsegs (Z_to_bv 64 (A + Z.of_nat i)) with
                    | Some b => bv_unsigned b =? bv_unsigned (nth i bs (Z_to_bv 8 0))
                    | None => false end)
    (seq 0 (length bs)).
Lemma pfw_bytes_rom : forall (W : world tfibsegs) m A bs,
  (forall i, (i < length bs)%nat -> aview tfibsegs (w_H W) m (A + Z.of_nat i) =
     option_map (fun b : byte => bv_unsigned b) (YKW.seg_rom tfibsegs (Z_to_bv 64 (A + Z.of_nat i)))) ->
  pfw_img_bytes A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m A bs.
Proof.
  intros W m A bs HV HB H0 H1. apply (pfw_bytes_view W m A bs); [|exact H0 | exact H1].
  intros i Hi. rewrite (HV i Hi). unfold pfw_img_bytes in HB.
  assert (Hk : In i (seq 0 (length bs))) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) HB i Hk) as H. cbv beta in H.
  destruct (YKW.seg_rom tfibsegs (Z_to_bv 64 (A + Z.of_nat i))) as [b|]; [|discriminate H].
  apply Z.eqb_eq in H. cbn [option_map]. rewrite H. reflexivity.
Qed.
Lemma pfw_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.
Lemma pfw_sltu0 : forall r : word, v_sltu (Z_to_bv 64 0) r = Z_to_bv 64 (if bv_unsigned r =? 0 then 0 else 1).
Proof.
  intros r. unfold v_sltu, c_ltu. rewrite bv_ltu_Z. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  pose proof (u64_range r) as R.
  destruct (Z.eqb_spec (bv_unsigned r) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (0 <? bv_unsigned r) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
(* ================================ the three footprint runs ================================ *)
(* the state at the strcmp trampoline in turn k (spf: the frame's base) *)
Definition pfw_call_ms (k : Z) (spf gp tp t0 t1 t2 x a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  MS (mkR (Z_to_bv 64 PFW_RET) spf gp tp t0 t1 t2 x (Z_to_bv 64 PCB.ASAN_K) x (Z_to_bv 64 (PFW_NAME k)) a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 k) (Z_to_bv 64 TRANS_PERS) (Z_to_bv 64 (TRANS_PERS + 24 * k)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 PFW_STRCMP) fc None m (seg_rom rsegs).
(* the state after the `ret`, with a0 = v *)
Definition pfw_ret_ms (v : Z) (rao spf gp tp t0 t1 t2 s0o s1o a1 a2 a3 a4 a5 a6 a7 s2o s3o s4o s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  MS (mkR rao (Z_to_bv 64 (bv_unsigned spf + 48)) gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
          s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (ret_pc rao) fc None m (seg_rom rsegs).

Lemma pfw_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bv_unsigned a0 <> 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 2 ^ 32 <= lo ->
    bytes_at rsegs m PCB.GOT_CELL_K (le8 (wa PCB.CELL_K)) -> bytes_at rsegs m PCB.CELL_K (le8 (wa PCB.ASAN_K)) ->
    bytes_at rsegs m (PCB.shadow_addr (TRANS_PERS + 8)) [Z_to_bv 8 0] ->
    bytes_at rsegs m (TRANS_PERS + 8) (le8 (wa (PFW_NAME 0))) ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 ->
    ExecF.rng RNG PCB.GOT_CELL_K 8 -> ExecF.rng RNG PCB.CELL_K 8 ->
    ExecF.rng RNG (PCB.shadow_addr (TRANS_PERS + 8)) 1 -> ExecF.rng RNG (TRANS_PERS + 8) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m', ms' = pfw_call_ms 0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7
                                 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m' /\
         munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFW_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo Ha0 ST LO L32 HGC HCK HSH HPN RFR RGC RCK RSH RPN.
  unfold pfw_call_ms. pfw_lits. unfold PCB.GOT_CELL_K, PCB.CELL_K, PCB.shadow_addr in *. unfold PCB.ASAN_K in *.
  cbn [Z.eqb] in *.
  change ((670464 + 8) / 8 + 2147450880) with 2147534689 in *. change (670464 + 8) with 670472 in *.
  pose proof (u64_range sp) as Rsp.
  pose proof (conj HGC (conj HCK (conj HSH (conj HPN I)))) as CELLS. clear HGC HCK HSH HPN.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  (* 0x8c050 - 0x8c068: the frame and the six saves *)
  do 7 step.
  (* 0x8c06c: beqz a0, not taken (x <> 0) *)
  step. if_false.
  match goal with MU' : munch _ m ?m1 |- _ => rename m1 into mA end.
  destruct CELLS as (HGC & HCK & HSH & HPN & _).
  apply (bytes_tp m mA _ _ _ _ MU) in HGC; [|rewrite length_le8; lia].
  apply (bytes_tp m mA _ _ _ _ MU) in HCK; [|rewrite length_le8; lia].
  apply (bytes_tp m mA _ _ _ _ MU) in HSH; [|cbn [length]; lia].
  apply (bytes_tp m mA _ _ _ _ MU) in HPN; [|rewrite length_le8; lia].
  pose proof (pfw_rd_all mA _ _ HGC) as RGC'. pose proof (pfw_rd_all mA _ _ HCK) as RCK'.
  pose proof (pfw_rd_all mA _ _ HSH) as RSH'. pose proof (pfw_rd_all mA _ _ HPN) as RPN'.
  rewrite length_le8 in RGC', RCK', RPN'. cbn [length] in RSH'.
  clear HGC HCK HSH HPN.
  (* 0x8c070 - 0x8c088: s0 = x, s2 = 0, s1 = the shadow base, s3 = personalities;
     0x8c08c - 0x8c0a8: turn 0, s4 = personalities, the shadow byte of personalities + 8 *)
  do 15 step.
  (* 0x8c0ac: bnez on the shadow byte, not taken *)
  step. if_false.
  (* 0x8c0b0 - 0x8c0b8: a1 = personalities[0].announce_name, a0 = s0, the call *)
  do 3 step.
  apply evtF_done. exists mA. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact FR].
Qed.

Lemma pfw_run2_F :
  forall (RNG : ExecF.footprint)
         (ra spf gp tp t0 t1 t2 x s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (rao s0o s1o s2o s3o s4o : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    s1 = Z_to_bv 64 PCB.ASAN_K -> s2 = Z_to_bv 64 0 -> s3 = Z_to_bv 64 TRANS_PERS -> s4 = Z_to_bv 64 TRANS_PERS ->
    2 ^ 32 <= bv_unsigned spf -> bv_unsigned spf + 48 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned spf) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
    bytes_at rsegs m (PCB.shadow_addr (TRANS_PERS + 32)) [Z_to_bv 8 0] ->
    bytes_at rsegs m (TRANS_PERS + 32) (le8 (wa (PFW_NAME 1))) ->
    ExecF.rng RNG (bv_unsigned spf) 48 ->
    ExecF.rng RNG (PCB.shadow_addr (TRANS_PERS + 32)) 1 -> ExecF.rng RNG (TRANS_PERS + 32) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => (bv_unsigned r = 0 /\ exists a1', ms' = pfw_ret_ms TRANS_PERS rao spf gp tp t0 t1 t2 s0o s1o a1' a2 a3 a4
                     a5 a6 a7 s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m) \/
                  (bv_unsigned r <> 0 /\ ms' = pfw_call_ms 1 spf gp tp t0 t1 t2 x a2 a3 a4 a5 a6 a7
                                 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m))
      (MS (mkR ra spf gp tp t0 t1 t2 x s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFW_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra spf gp tp t0 t1 t2 x s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    rao s0o s1o s2o s3o s4o F fc m -> -> -> -> L32 Ltop FR HSH HPN RFR RSH RPN.
  unfold pfw_call_ms, pfw_ret_ms. pfw_lits. unfold PCB.shadow_addr in *. unfold PCB.ASAN_K in *.
  cbn [Z.eqb] in *.
  change ((670464 + 32) / 8 + 2147450880) with 2147534692 in *. change (670464 + 32) with 670496 in *.
  pose proof (pfw_rd_all m _ _ HSH) as RSH'. pose proof (pfw_rd_all m _ _ HPN) as RPN'.
  rewrite length_le8 in RPN'. cbn [length] in RSH'.
  clear HSH HPN.
  (* 0x8c0bc - 0x8c0c8: a0 = (r <> 0), a1 = a0 & (s2 ^ 1), s2 = 1 *)
  do 4 step.
  rewrite pfw_sltu0.
  destruct (Z.eqb_spec (bv_unsigned r) 0) as [E|E].
  - (* 0x8c0cc: bnez a1 not taken; a0 = s4; the epilogue and ret *)
    step. if_false.
    do 10 step.
    apply evtF_done. left. split; [exact E|]. eexists. reflexivity.
  - (* bnez a1 taken: turn 1 to the call *)
    step. if_true.
    do 8 step.
    step. if_false.
    do 3 step.
    apply evtF_done. right. split; [exact E | reflexivity].
Qed.

Lemma pfw_run3_F :
  forall (RNG : ExecF.footprint)
         (ra spf gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (rao s0o s1o s2o s3o s4o : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    s2 = Z_to_bv 64 1 -> s4 = Z_to_bv 64 (TRANS_PERS + 24) ->
    2 ^ 32 <= bv_unsigned spf -> bv_unsigned spf + 48 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned spf) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
    ExecF.rng RNG (bv_unsigned spf) 48 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1', ms' = pfw_ret_ms (if bv_unsigned r =? 0 then TRANS_PERS + 24 else 0) rao spf gp tp t0 t1 t2
                     s0o s1o a1' a2 a3 a4 a5 a6 a7 s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra spf gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFW_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra spf gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    rao s0o s1o s2o s3o s4o F fc m -> -> L32 Ltop FR RFR.
  unfold pfw_ret_ms. pfw_lits.
  do 4 step.
  rewrite pfw_sltu0.
  destruct (Z.eqb_spec (bv_unsigned r) 0) as [E|E].
  - step. if_false.
    do 10 step.
    apply evtF_done. eexists. reflexivity.
  - step. if_false.
    do 10 step.
    apply evtF_done. eexists. reflexivity.
Qed.

(* ================================ the names' shadow ================================ *)
Lemma pfw_z1_rd {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v :
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 ->
  aview tfibsegs (w_H W) mem a = Some v.
Proof.
  intros [M _] Hin Hv.
  assert (HK : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) by (eapply am_const; exact M).
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as Hc.
  unfold cell_holds, z1, c1 in Hc. cbn [aeval c_at c_w c_val] in Hc.
  specialize (Hc 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hc. rewrite Z.add_0_r in Hc.
  rewrite Hc. f_equal. apply pfw_le_byte1. exact Hv.
Qed.
(* the rows of transport_cells the walk reads *)
Lemma pfw_cells_rows (B : asyms) : transport_cells B -> forall ly,
  decode_zshadow_at B TRANS_PNAME0 (TRANS_PNAME0 + 8) /\
  In (z1 (ANum (PCB.shadow_addr (TRANS_PNAME0 + 8))) 1) (as_const B ly) /\
  decode_zshadow_at B TRANS_PNAME1 (TRANS_PNAME1 + 8) /\
  In (z1 (ANum (PCB.shadow_addr (TRANS_PNAME1 + 8))) 1) (as_const B ly) /\
  decode_zshadow_at B TRANS_PERS (TRANS_PERS + 48).
Proof.
  intros HC ly. pose proof (HC ly) as H.
  repeat match type of H with _ /\ _ => let H1 := fresh "R" in destruct H as [H1 H] end.
  repeat split; assumption.
Qed.
(* a 9-byte name: its 8 payload bytes have shadow 0, the ninth shadow 1, and the group of 8 shadow bytes [G, G + 8)
   around them is visible; on image B the two names lie in two groups (0x7fffc230 for TRANS_PNAME0, 0x7fffc238 for
   TRANS_PNAME1) *)
Lemma pfw_name_sh : forall (rd : Z -> option Z) y G n,
  (y = TRANS_PNAME0 /\ G = 2147467824 \/ y = TRANS_PNAME1 /\ G = 2147467832) -> 0 < n <= 9 ->
  (forall s, G <= s < G + 8 -> rd s <> None) ->
  rd (PCB.shadow_addr y) = Some 0 -> rd (PCB.shadow_addr (y + 8)) = Some 1 ->
  range_addressable rd SHADOW_OFF y n /\ shadow_hull_vis rd y n.
Proof.
  intros rd y G n Hy Hn Hv H0 H1. split.
  - intros x Hx. destruct (Z_lt_dec x (y + 8)) as [Hl|Hl].
    + exists 0. split; [|left; reflexivity].
      replace (shadow_of_addr SHADOW_OFF x) with (PCB.shadow_addr y); [exact H0|].
      unfold shadow_of_addr, PCB.shadow_addr, PCB.ASAN_K, SHADOW_OFF.
      destruct Hy as [[-> ->] | [-> ->]]; unfold TRANS_PNAME0, TRANS_PNAME1 in *; Z.div_mod_to_equations; lia.
    + exists 1. split.
      * replace (shadow_of_addr SHADOW_OFF x) with (PCB.shadow_addr (y + 8)); [exact H1|].
        unfold shadow_of_addr, PCB.shadow_addr, PCB.ASAN_K, SHADOW_OFF.
        destruct Hy as [[-> ->] | [-> ->]]; unfold TRANS_PNAME0, TRANS_PNAME1 in *; Z.div_mod_to_equations; lia.
      * right. destruct Hy as [[-> ->] | [-> ->]]; unfold TRANS_PNAME0, TRANS_PNAME1 in *; Z.div_mod_to_equations; lia.
  - intros s Hs. apply Hv. unfold YG0f.shadow_addr, SHADOW_OFF in Hs.
    destruct Hy as [[-> ->] | [-> ->]]; unfold TRANS_PNAME0, TRANS_PNAME1 in *; Z.div_mod_to_equations; lia.
Qed.
(* the 8 shadow bytes of a group, each a value of the record *)
Lemma pfw_group_vis : forall (rd : Z -> option Z) G (v0 v1 v2 v3 v4 v5 v6 v7 : Z),
  rd G = Some v0 -> rd (G + 1) = Some v1 -> rd (G + 2) = Some v2 -> rd (G + 3) = Some v3 ->
  rd (G + 4) = Some v4 -> rd (G + 5) = Some v5 -> rd (G + 6) = Some v6 -> rd (G + 7) = Some v7 ->
  forall s, G <= s < G + 8 -> rd s <> None.
Proof.
  intros rd G v0 v1 v2 v3 v4 v5 v6 v7 E0 E1 E2 E3 E4 E5 E6 E7 s Hs.
  assert (Hc : s = G \/ s = G + 1 \/ s = G + 2 \/ s = G + 3 \/ s = G + 4 \/ s = G + 5 \/ s = G + 6 \/ s = G + 7)
    by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    first [rewrite E0 | rewrite E1 | rewrite E2 | rewrite E3 | rewrite E4 | rewrite E5 | rewrite E6 | rewrite E7];
    discriminate.
Qed.
Lemma pfw_names_shadow {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md :
  transport_cells B -> trans_pfrom_cells B -> @AR rc tfibsegs B ly S W mem md ->
  forall y n, (y = TRANS_PNAME0 \/ y = TRANS_PNAME1) -> 0 < n <= 9 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y n /\
  shadow_hull_vis (aview tfibsegs (w_H W) mem) y n.
Proof.
  intros HC HP HAR y n Hy Hn.
  destruct (pfw_cells_rows B HC ly) as (Z0 & C0 & Z1 & C1 & _).
  destruct HP as (ZL & ZR & HPly). destruct (HPly ly) as (G0 & G1 & G2 & G3).
  (* the group of TRANS_PNAME0: the 32 bytes before it (zero shadow), the name, its two guard granules *)
  pose proof (decode_zshadow_rd B ly S W mem md (TRANS_PNAME0 - 32) TRANS_PNAME0 (TRANS_PNAME0 - 32) HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZL) as U0.
  pose proof (decode_zshadow_rd B ly S W mem md (TRANS_PNAME0 - 32) TRANS_PNAME0 (TRANS_PNAME0 - 24) HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZL) as U1.
  pose proof (decode_zshadow_rd B ly S W mem md (TRANS_PNAME0 - 32) TRANS_PNAME0 (TRANS_PNAME0 - 16) HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZL) as U2.
  pose proof (decode_zshadow_rd B ly S W mem md (TRANS_PNAME0 - 32) TRANS_PNAME0 (TRANS_PNAME0 - 8) HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZL) as U3.
  pose proof (decode_zshadow_rd B ly S W mem md TRANS_PNAME0 (TRANS_PNAME0 + 8) TRANS_PNAME0 HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) Z0) as V0.
  pose proof (pfw_z1_rd B ly S W mem md _ 1 HAR C0 ltac:(lia)) as V1.
  pose proof (pfw_z1_rd B ly S W mem md _ 0xf9 HAR G0 ltac:(lia)) as V2.
  pose proof (pfw_z1_rd B ly S W mem md _ 0xf9 HAR G1 ltac:(lia)) as V3.
  (* the group of TRANS_PNAME1: the name, its two guard granules, the 32 bytes after it (zero shadow) *)
  pose proof (decode_zshadow_rd B ly S W mem md TRANS_PNAME1 (TRANS_PNAME1 + 8) TRANS_PNAME1 HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) Z1) as V4.
  pose proof (pfw_z1_rd B ly S W mem md _ 1 HAR C1 ltac:(lia)) as V5.
  pose proof (pfw_z1_rd B ly S W mem md _ 0xf9 HAR G2 ltac:(lia)) as V6.
  pose proof (pfw_z1_rd B ly S W mem md _ 0xf9 HAR G3 ltac:(lia)) as V7.
  pose proof (decode_zshadow_rd B ly S W mem md (TRANS_PNAME1 + 32) (TRANS_PNAME1 + 64) (TRANS_PNAME1 + 32) HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZR) as U4.
  pose proof (decode_zshadow_rd B ly S W mem md (TRANS_PNAME1 + 32) (TRANS_PNAME1 + 64) (TRANS_PNAME1 + 40) HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZR) as U5.
  pose proof (decode_zshadow_rd B ly S W mem md (TRANS_PNAME1 + 32) (TRANS_PNAME1 + 64) (TRANS_PNAME1 + 48) HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZR) as U6.
  pose proof (decode_zshadow_rd B ly S W mem md (TRANS_PNAME1 + 32) (TRANS_PNAME1 + 64) (TRANS_PNAME1 + 56) HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZR) as U7.
  assert (HV0 : forall s, 2147467824 <= s < 2147467824 + 8 -> aview tfibsegs (w_H W) mem s <> None).
  { apply (pfw_group_vis _ 2147467824 0 0 0 0 0 1 0xf9 0xf9).
    - change 2147467824 with (FCells.shadow_addr (TRANS_PNAME0 - 32)). exact U0.
    - change (2147467824 + 1) with (FCells.shadow_addr (TRANS_PNAME0 - 24)). exact U1.
    - change (2147467824 + 2) with (FCells.shadow_addr (TRANS_PNAME0 - 16)). exact U2.
    - change (2147467824 + 3) with (FCells.shadow_addr (TRANS_PNAME0 - 8)). exact U3.
    - change (2147467824 + 4) with (FCells.shadow_addr TRANS_PNAME0). exact V0.
    - change (2147467824 + 5) with (PCB.shadow_addr (TRANS_PNAME0 + 8)). exact V1.
    - change (2147467824 + 6) with (PCB.shadow_addr (TRANS_PNAME0 + 16)). exact V2.
    - change (2147467824 + 7) with (PCB.shadow_addr (TRANS_PNAME0 + 24)). exact V3. }
  assert (HV1 : forall s, 2147467832 <= s < 2147467832 + 8 -> aview tfibsegs (w_H W) mem s <> None).
  { apply (pfw_group_vis _ 2147467832 0 1 0xf9 0xf9 0 0 0 0).
    - change 2147467832 with (FCells.shadow_addr TRANS_PNAME1). exact V4.
    - change (2147467832 + 1) with (PCB.shadow_addr (TRANS_PNAME1 + 8)). exact V5.
    - change (2147467832 + 2) with (PCB.shadow_addr (TRANS_PNAME1 + 16)). exact V6.
    - change (2147467832 + 3) with (PCB.shadow_addr (TRANS_PNAME1 + 24)). exact V7.
    - change (2147467832 + 4) with (FCells.shadow_addr (TRANS_PNAME1 + 32)). exact U4.
    - change (2147467832 + 5) with (FCells.shadow_addr (TRANS_PNAME1 + 40)). exact U5.
    - change (2147467832 + 6) with (FCells.shadow_addr (TRANS_PNAME1 + 48)). exact U6.
    - change (2147467832 + 7) with (FCells.shadow_addr (TRANS_PNAME1 + 56)). exact U7. }
  destruct Hy as [-> | ->].
  - exact (pfw_name_sh _ TRANS_PNAME0 2147467824 n (or_introl (conj eq_refl eq_refl)) Hn HV0 V0 V1).
  - exact (pfw_name_sh _ TRANS_PNAME1 2147467832 n (or_intror (conj eq_refl eq_refl)) Hn HV1 V4 V5).
Qed.
(* the name's 9 bytes as a read range *)
Lemma pfw_name_rd {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md y s :
  transport_cells B -> trans_pfrom_cells B -> @AR rc tfibsegs B ly S W mem md ->
  (y = TRANS_PNAME0 \/ y = TRANS_PNAME1) -> pfw_cstr_at W mem y s -> length s = 8%nat ->
  decode_rd_ok W mem y (Z.of_nat (length s) + 1).
Proof.
  intros HC HP HAR Hy CS Hl. rewrite Hl. change (Z.of_nat 8 + 1) with 9.
  destruct (pfw_names_shadow B ly S W mem md HC HP HAR y 9 Hy ltac:(lia)) as [Ha Hh].
  split; [intros a Ha'; apply (pfw_cstr_rd W mem y s CS); rewrite Hl; cbn; lia|].
  split; [exact Ha|]. split; [exact Hh|].
  destruct Hy as [-> | ->]; unfold amem_range, kLowMemEnd, TRANS_PNAME0, TRANS_PNAME1; lia.
Qed.

(* ================================ the call of the strcmp wrapper ================================ *)
Section s. Context {fx : YKW.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
(* The wrapper's contract (the statement's astrcmp_realizes) at a journal, on two C strings sx at x and sy at y,
   each a read range of its length + 1 bytes off the wrapper's 2 * ESTACK window below sp = sp0 + o. *)
Lemma pfw_strcmp_cstr_at : forall pc, @astrcmp_realizes fx rc tfibsegs B pc ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y sx sy (o raw : Z),
  @ajournal rc YE2k.tfib_sink_head tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
  YKW.getr regsT (Z_to_bv 5 10) = w64 x -> YKW.getr regsT (Z_to_bv 5 11) = w64 y -> 0 < x -> 0 < y ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  YKW.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YKW.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  YKW.getr regsT (Z_to_bv 5 1) = w64 raw -> 0 <= raw < 2 ^ 64 -> YK0s.ret_ok (w64 raw) ->
  Z.of_nat (length sy) + 1 < 2 ^ 32 ->
  pfw_cstr_at W memT x sx -> pfw_cstr_at W memT y sy ->
  decode_rd_ok W memT x (Z.of_nat (length sx) + 1) -> decode_rd_ok W memT y (Z.of_nat (length sy) + 1) ->
  (forall a, x <= a < x + Z.of_nat (length sx) + 1 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a < y + Z.of_nat (length sy) + 1 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regsT memT mdc)
  (fun W2 cf => W2 = W /\ exists regs2 mem2 md2,
     cf = @cfg_at fx tfibsegs raw regs2 mem2 md2 /\
     @ajournal rc YE2k.tfib_sink_head tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
     aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\
     YKW.getr regs2 (Z_to_bv 5 10) = w64 (pfw_strcmpZ sx sy) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
        aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
  intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y sx sy o raw
    HJ Ha0 Ha1 Hx0 Hy0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw0 Hraw Hlen [Nx AX] [Ny AY] Rx Ry Wx Wy.
  assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
  destruct (pfw_cs_k_le sx sy) as [Kx Ky].
  destruct (pfw_cs_k_spec sx sy Nx Ny) as (P1 & P2 & _).
  set (kk := pfw_cs_k sx sy) in *.
  pose proof (trans_rd_ok_sub W memT x _ x (Z.of_nat kk + 1) Rx ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hxr & Hxa & Hxh & Hxm & Hxq & Hxn).
  pose proof (trans_rd_ok_sub W memT y _ y (Z.of_nat kk + 1) Ry ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hyr & Hya & Hyh & Hym & Hyq & Hyn).
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
  { eapply ecall_pre_at; [exact HJ | exact Hsp' | exact Hal | exact Hneg | lia | | exact Hgp | exact Htp].
    change (YK0s.ret_ok (YKW.getr regsT (Z_to_bv 5 1))). rewrite Hra. exact Hraw. }
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; lia).
  assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
    by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; lia).
  eapply SRr_mono.
  { apply (AM lyc Sc W regsT memT mdc x y (Z.of_nat kk) (nth kk (sx ++ [0]) 0) (nth kk (sy ++ [0]) 0)
             HPRE Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 ltac:(lia) ltac:(lia) ltac:(lia)).
    - split; [lia|]. split.
      + intros i Hi. destruct (P1 (Z.to_nat i) ltac:(lia)) as [Eq Nz].
        exists (nth (Z.to_nat i) (sx ++ [0]) 0).
        replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
        replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
        split; [apply AX; lia|]. split; [rewrite Eq; apply AY; lia | exact Nz].
      + split; [apply AX; lia|]. split; [apply AY; lia | exact P2].
    - intros a Ha. split; [apply Hxr; exact Ha|]. rewrite Hsp'. intros C. apply (Wx a); lia.
    - intros a Ha. split; [apply Hyr; exact Ha|]. rewrite Hsp'. intros C. apply (Wy a); lia.
    - intros a Ha. rewrite Hsp'. apply Wx. lia.
    - intros a Ha. rewrite Hsp'. apply Wy. lia.
    - exact Hxm.
    - exact Hym.
    - exact Hxa.
    - exact Hxh.
    - exact Hya.
    - exact Hyh. }
  cbv beta. intros W2 cf _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
  rewrite Hsp' in Hfr.
  split; [reflexivity|]. exists regs2, mem2, md2.
  split.
  { change (raZ regsT) with (bv_unsigned (YKW.getr regsT (Z_to_bv 5 1))). rewrite Hra. unfold w64.
    rewrite unsigned_lit by lia. reflexivity. }
  split.
  { eapply (ajournal_after_write tfibsegs B LAWS decode_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj
             mem2 md2 (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
    - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
    - exact Hpres2.
    - exact Hsame.
    - intros a Ha; left; left; lia.
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
End s.

(* ================================ the post ================================ *)
Lemma pfw_pres_groups : forall regs regsF : bvmap 5 word,
  YKW.getr regsF (Z_to_bv 5 2) = YKW.getr regs (Z_to_bv 5 2) ->
  (forall r, r = 3 \/ r = 4 \/ 21 <= r <= 27 -> YKW.getr regsF (Z_to_bv 5 r) = YKW.getr regs (Z_to_bv 5 r)) ->
  (forall r, r = 8 \/ r = 9 \/ 18 <= r <= 20 -> YKW.getr regsF (Z_to_bv 5 r) = YKW.getr regs (Z_to_bv 5 r)) ->
  aregs_preserved regs regsF.
Proof.
  intros regs regsF E2 E3 E8 r Hr. unfold acallee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [exact E2 | apply E3; lia | apply E3; lia | apply E8; lia | apply E8; lia |].
  destruct (Z_le_gt_dec r 20); [apply E8; lia | apply E3; lia].
Qed.

Section close. Context {fx : YKW.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Lemma pfw_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs tb memF mdF regsF,
  AR_laws segs B -> ameter_laws MT ->
  @ajournal rc YE2k.tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  @ajournal rc YE2k.tfib_sink_head segs B PFROM_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memF mdF 0 ->
  sp0 - STK <= spZ regs - PFROM_STK -> spZ regs <= sp0 ->
  aregs_preserved regs regsF -> YKW.getr regsF (Z_to_bv 5 10) = w64 (trans_pfrom_res tb) ->
  transport_pfrom_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tb W
    (mkCfg (YKW.mkst regsF (YKW.getr regs (Z_to_bv 5 1)) memF (YKW.seg_rom segs)) mdF).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs tb memF mdF regsF LAWS MTL HJ IJ Hlo Hhi KPRES HRES.
  unfold transport_pfrom_post, decode_cg_post.
  exists lyc, Sc, regsF, memF, mdF, 0.
  split; [reflexivity|].
  split; [unfold PFROM_EV; lia|].
  split.
  { change own with ([] ++ own).
    apply (ajournal_sub segs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             PFROM_STK (spZ regs) [] [] lyc Sc W memF mdF 0 HJ IJ Hlo Hhi).
    intros a (r & Hr & _). destruct Hr. }
  split; [exact KPRES|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B decode_segs_low PFROM_STK (spZ regs) [] [] lyc Sc W memc mdc
             lyc Sc W memF mdF 0 (fun _ => False) IJ (proj1 HJ)).
    - intros a (r & Hr & _). destruct Hr.
    - intros b m i Hb _ _. exact Hb.
    - exact sink_closed_nil. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  exact HRES.
Qed.
End close.

(* ================================ the walk ================================ *)
Ltac pfw_reg HX := etransitivity; [exact (decode_getr_xeqv _ _ HX _) | reflexivity].
Ltac pfw_cell_in := unfold decode_asan_cell_ranges; cbn [In]; repeat (first [left; reflexivity | right]).
Ltac pfw_cases3 r :=
  let Hc := fresh "Hc" in
  assert (Hc : r = 3 \/ r = 4 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]].
Ltac pfw_cases8 r :=
  let Hc := fresh "Hc" in
  assert (Hc : r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20) by lia;
  destruct Hc as [->|[->|[->|[->| ->]]]].

Section walk. Context {fx : YKW.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

Lemma pfw_holds : @transport_diginet_personality_from_name_cg_holds_stmt fx rc B MT.
Proof.
  unfold transport_diginet_personality_from_name_cg_holds_stmt, transport_diginet_personality_from_name_cg.
  intros HCELLS HPC HROU HRNE LAWS MTL STRCMP.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs x tb
    HJ Hra Hra4 Hgp Htp H10 Hal Hwlo Hwhi Hx0 HG8 HIN HSRC HOFF HROM HNEV.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hstatic & F5 & HQT).
  pose proof Hstatic as (H16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (EPS : PFROM_STK = 8240) by reflexivity.
  assert (HSPLO : YM05.alloc_ceiling + PFROM_STK <= spZ regs) by lia.
  assert (HSPHI : spZ regs <= 2 ^ 47) by lia.
  (* ---- the string ---- *)
  assert (Hn0 : 0 < Z.of_nat (length tb)) by (destruct tb as [|b0 tb']; [destruct HIN | cbn [length]; lia]).
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc x (Z.of_nat (length tb)) HAR HSRC Hn0) as HRD.
  pose proof HRD as (_ & _ & _ & HAM & Hx0' & Hx63).
  destruct (pfw_split tb HIN) as (sx & rest & Htb & NSX).
  pose proof (pfw_nz sx NSX) as NX.
  set (xs := map DSW.bz sx) in *.
  assert (Lxs : Z.of_nat (length xs) + 1 <= Z.of_nat (length tb))
    by (unfold xs; rewrite Htb, length_app, length_map; cbn [length]; lia).
  assert (CX0 : pfw_cstr_at W memc x xs).
  { apply (pfw_cstr_of_garr8 W memc x xs (map DSW.bz rest)); [|exact NX].
    rewrite Htb, map_app in HG8. exact HG8. }
  assert (RX0 : decode_rd_ok W memc x (Z.of_nat (length xs) + 1))
    by exact (trans_rd_ok_sub W memc x _ x (Z.of_nat (length xs) + 1) HRD ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (HOFX : x + Z.of_nat (length xs) + 1 <= spZ regs - PFROM_STK \/ spZ regs <= x)
    by (unfold decode_off_win in HOFF; lia).
  (* ---- the names ---- *)
  assert (CN0 : pfw_cstr_at W memc TRANS_PNAME0 CCW.NAME_C24).
  { apply (pfw_cstr_rom W memc TRANS_PNAME0 CCW.NAME_C24 HROM); [|vm_compute; reflexivity].
    intros j Hj. rewrite pfw_len_c24 in Hj. apply (pfw_ro_rd TRANS_PNAME0 9); [pfw_in | lia]. }
  assert (CN1 : pfw_cstr_at W memc TRANS_PNAME1 CCW.NAME_PC).
  { apply (pfw_cstr_rom W memc TRANS_PNAME1 CCW.NAME_PC HROM); [|vm_compute; reflexivity].
    intros j Hj. rewrite pfw_len_pc in Hj. apply (pfw_ro_rd TRANS_PNAME1 9); [pfw_in | lia]. }
  pose proof (pfw_name_rd B lyc Sc W memc mdc TRANS_PNAME0 CCW.NAME_C24 HCELLS HPC HAR (or_introl eq_refl) CN0 eq_refl)
    as RN0.
  pose proof (pfw_name_rd B lyc Sc W memc mdc TRANS_PNAME1 CCW.NAME_PC HCELLS HPC HAR (or_intror eq_refl) CN1 eq_refl)
    as RN1.
  (* ---- the inner journal at the entry ---- *)
  assert (JI0 : @ajournal rc YE2k.tfib_sink_head tfibsegs B PFROM_STK (spZ regs) [] lyc Sc W memc mdc []
                  lyc Sc W memc mdc 0).
  { apply (@ajournal_sub_init rc YE2k.tfib_sink_head tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
             mdc k PFROM_STK (spZ regs) [] (spZ regs - sp0) HJ ltac:(lia)
             ltac:(rewrite Zminus_mod, Hal, H16; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)). }
  pose proof JI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
  (* ---- the reads of the first run at the entry ---- *)
  pose proof (decode_cells_asan B HCELLS lyc Sc W memc mdc HAR) as (HCK & HGC & _).
  destruct (pfw_cells_rows B HCELLS lyc) as (_ & _ & _ & _ & ZPS).
  pose proof (decode_zshadow_rd B lyc Sc W memc mdc TRANS_PERS (TRANS_PERS + 48) (TRANS_PERS + 8) HAR
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZPS) as VS0.
  assert (BS0 : bytes_at rsegs memc (PCB.shadow_addr (TRANS_PERS + 8)) [Z_to_bv 8 0])
    by (apply (pfw_bytes1 W memc); [exact VS0 | unfold PCB.shadow_addr, PCB.ASAN_K, TRANS_PERS; lia]).
  assert (BP0 : bytes_at rsegs memc (TRANS_PERS + 8) (le8 (wa (PFW_NAME 0)))).
  { apply (pfw_bytes_rom W memc); [|vm_compute; reflexivity | unfold TRANS_PERS; lia | rewrite length_le8; unfold TRANS_PERS; lia].
    intros i Hi. rewrite length_le8 in Hi. apply HROM. apply (pfw_ro_rd TRANS_PERS 48); [pfw_in | lia]. }
  assert (E10 : YKW.getr regs (Z_to_bv 5 10) = Z_to_bv 64 x) by exact H10.
  (* ---- the run from the entry to the first call ---- *)
  eapply (@decode_run fx W regs memc mdc PFW_ENTRY).
  { unfold LCW.ms_of_regs. rewrite E10.
    eapply pfw_run1_F with (lo := spZ regs - 48).
    - rewrite unsigned_lit by lia. exact Hx0.
    - apply (decode_stk_present (w_H W) memc (spZ regs - 48) (spZ regs)); [lia | lia |].
      intros a Ha. apply Hpres0. lia.
    - change (bv_unsigned (YKW.getr regs (Z_to_bv 5 2))) with (spZ regs). lia.
    - lia.
    - exact HGC.
    - exact HCK.
    - exact BS0.
    - exact BP0.
    - change (bv_unsigned (YKW.getr regs (Z_to_bv 5 2))) with (spZ regs).
      apply (decode_rng_vis W); [lia | lia |]. intros i Hi.
      destruct (Hpres0 (spZ regs - 48 + i) ltac:(lia)) as [Hh _]. exact Hh.
    - apply (decode_rng_vis W); [unfold PCB.GOT_CELL_K; lia | unfold PCB.GOT_CELL_K; lia |].
      intros i Hi. eapply decode_cell_visible; [pfw_cell_in | exact Hi].
    - apply (decode_rng_vis W); [unfold PCB.CELL_K; lia | unfold PCB.CELL_K; lia |].
      intros i Hi. eapply decode_cell_visible; [pfw_cell_in | exact Hi].
    - apply (decode_rng_vis W); [unfold PCB.shadow_addr, PCB.ASAN_K, TRANS_PERS; lia
                            | unfold PCB.shadow_addr, PCB.ASAN_K, TRANS_PERS; lia |].
      intros i Hi. replace (PCB.shadow_addr (TRANS_PERS + 8) + i) with (FCells.shadow_addr (TRANS_PERS + 8)) by lia.
      exact (pfw_aview_vis W memc _ 0 VS0).
    - apply (decode_rng_vis W); [unfold TRANS_PERS; lia | unfold TRANS_PERS; lia |].
      intros i Hi. apply (pfw_ro_vis W memc _ HROM). apply (pfw_ro_rd TRANS_PERS 48); [pfw_in | lia]. }
  (* ---- the state at the first call ---- *)
  intros ms0 msA mdA HP EQVA _ SBMA.
  destruct HP as (m1 & Hms0 & MU & WM & FR). subst ms0.
  unfold pfw_call_ms in EQVA.
  destruct (decode_eqv_mkst _ _ _ _ EQVA) as (RA & -> & HXA). clear EQVA.
  change (bv_unsigned (YKW.getr regs (Z_to_bv 5 2))) with (spZ regs) in MU, FR, HXA.
  (* the inner journal after the six saves *)
  assert (MUw : forall x0 : word, ~ (spZ regs - 48 <= bv_unsigned x0 < spZ regs) ->
            mrestrict (w_H W) m1 x0 = mrestrict (w_H W) memc x0).
  { intros x0 Hx. unfold mrestrict. rewrite (MU x0); [reflexivity|]. cbn [outside].
    split; [lia | exact I]. }
  assert (MGw : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) m1)).
  { intros x0 Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x0) eqn:Ehx; intros Hx; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x0) (spZ regs - 48)) as [Hl|Hl];
      [rewrite (MU x0); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
    destruct (Z_lt_le_dec (bv_unsigned x0) (spZ regs)) as [Hh|Hh];
      [|rewrite (MU x0); [exact Hx | cbn [outside]; split; [lia | exact I]]].
    assert (Hw : wview rsegs m1 x0 <> None).
    { refine (WM x0 _). unfold wview. destruct (memc x0) as [b|] eqn:Em;
        [discriminate | exfalso; first [exact (Hx Em) | exact (Hx eq_refl)]]. }
    unfold wview in Hw. destruct (m1 x0) as [b|] eqn:Em1; [discriminate|]. exfalso.
    rewrite (find_segment_none rsegs (bv_unsigned x0)) in Hw; [exact (Hw eq_refl)|].
    intros Him. pose proof (decode_segs_low _ Him) as Hlow. unfold kLowMemEnd in Hlow. lia. }
  assert (MHw : forall x0 : word, w_H W x0 = true -> m1 x0 = memc x0).
  { intros x0 Hx.
    destruct (Z_lt_le_dec (bv_unsigned x0) (spZ regs - 48)) as [Hl|Hl];
      [apply (MU x0); cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x0) (spZ regs)) as [Hh|Hh];
      [|apply (MU x0); cbn [outside]; split; [lia | exact I]].
    exfalso.
    pose proof (proj1 (Hpres0 (bv_unsigned x0) ltac:(lia))) as Hhx.
    rewrite Z_to_bv_bv_unsigned in Hhx. congruence. }
  assert (IJ1 : @ajournal rc YE2k.tfib_sink_head tfibsegs B PFROM_STK (spZ regs) [] lyc Sc W memc mdc []
                  lyc Sc W m1 mdA 0).
  { apply (@ajournal_exec rc YE2k.tfib_sink_head tfibsegs B LAWS decode_segs_low PFROM_STK (spZ regs) []
             lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 mdA
             (fun a => spZ regs - 48 <= a < spZ regs) JI0 MUw MGw MHw SBMA).
    intros a Ha. left. lia. }
  pose proof IJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PFROM_STK <= a < spZ regs) ->
            aview segs (w_H W) m1 a = aview segs (w_H W) memc a).
  { intros a Ha Hn. apply (aview_eq_of segs). apply MUw. rewrite unsigned_lit by lia. lia. }
  (* the registers at the first call *)
  assert (G1 : YKW.getr RA (Z_to_bv 5 1) = Z_to_bv 64 PFW_RET) by pfw_reg HXA.
  assert (G2 : YKW.getr RA (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -48)) by pfw_reg HXA.
  assert (G3 : YKW.getr RA (Z_to_bv 5 3) = YKW.getr regs (Z_to_bv 5 3)) by pfw_reg HXA.
  assert (G4 : YKW.getr RA (Z_to_bv 5 4) = YKW.getr regs (Z_to_bv 5 4)) by pfw_reg HXA.
  assert (G8 : YKW.getr RA (Z_to_bv 5 8) = Z_to_bv 64 x) by pfw_reg HXA.
  assert (G9 : YKW.getr RA (Z_to_bv 5 9) = Z_to_bv 64 PCB.ASAN_K) by pfw_reg HXA.
  assert (G10 : YKW.getr RA (Z_to_bv 5 10) = Z_to_bv 64 x) by pfw_reg HXA.
  assert (G11 : YKW.getr RA (Z_to_bv 5 11) = Z_to_bv 64 TRANS_PNAME0) by pfw_reg HXA.
  assert (G18 : YKW.getr RA (Z_to_bv 5 18) = Z_to_bv 64 0) by pfw_reg HXA.
  assert (G19 : YKW.getr RA (Z_to_bv 5 19) = Z_to_bv 64 TRANS_PERS) by pfw_reg HXA.
  assert (G20 : YKW.getr RA (Z_to_bv 5 20) = Z_to_bv 64 TRANS_PERS) by pfw_reg HXA.
  assert (P1 : forall r, r = 3 \/ r = 4 \/ 21 <= r <= 27 ->
            YKW.getr RA (Z_to_bv 5 r) = YKW.getr regs (Z_to_bv 5 r))
    by (intros r Hr; pfw_cases3 r; pfw_reg HXA).
  assert (GSP : spZ RA = spZ regs + -48).
  { change (spZ RA) with (bv_unsigned (YKW.getr RA (Z_to_bv 5 2))).
    rewrite G2, unsigned_lit by lia. reflexivity. }
  (* the strings at the first call *)
  assert (CX1 : pfw_cstr_at W m1 x xs)
    by (apply (pfw_cstr_kept W memc m1 x xs (spZ regs - PFROM_STK) (spZ regs) CX0 KE1); lia).
  assert (CN01 : pfw_cstr_at W m1 TRANS_PNAME0 CCW.NAME_C24)
    by (apply (pfw_cstr_kept W memc m1 TRANS_PNAME0 CCW.NAME_C24 (spZ regs - PFROM_STK) (spZ regs) CN0 KE1);
        rewrite ?pfw_len_c24; unfold TRANS_PNAME0; lia).
  assert (RX1 : decode_rd_ok W m1 x (Z.of_nat (length xs) + 1)).
  { apply (trans_rd_ok_view W W memc m1 x _ RX0).
    - intros a Ha. apply KE1; lia.
    - intros s Hs. apply KE1; unfold kLowMemEnd, kHighShadowEnd in Hs; lia. }
  assert (RN01 : decode_rd_ok W m1 TRANS_PNAME0 (Z.of_nat (length CCW.NAME_C24) + 1)).
  { apply (trans_rd_ok_view W W memc m1 _ _ RN0).
    - intros a Ha. rewrite pfw_len_c24 in Ha. apply KE1; unfold TRANS_PNAME0 in Ha; lia.
    - intros s Hs. apply KE1; unfold kLowMemEnd, kHighShadowEnd in Hs; lia. }
  (* ---- the first call: strcmp(x, "CNTRL|24") ---- *)
  eapply SRr_bind.
  { apply (pfw_strcmp_cstr_at B LAWS PFW_STRCMP (STRCMP fx) W RA m1 PFROM_STK (spZ regs) [] lyc Sc W memc mdc
             [] lyc Sc mdA 0 x TRANS_PNAME0 xs CCW.NAME_C24 (-48) PFW_RET IJ1).
    - exact G10.
    - exact G11.
    - lia.
    - unfold TRANS_PNAME0; lia.
    - exact GSP.
    - reflexivity.
    - lia.
    - lia.
    - rewrite G3. exact Hgp.
    - rewrite G4. exact Htp.
    - exact G1.
    - unfold PFW_RET; pfw_lits; lia.
    - apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - rewrite pfw_len_c24. lia.
    - exact CX1.
    - exact CN01.
    - exact RX1.
    - exact RN01.
    - intros a Ha. lia.
    - intros a Ha. rewrite pfw_len_c24 in Ha. unfold TRANS_PNAME0 in Ha. lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & IJ2 & HP2 & SB2 & HV2 & HK2 & HPR2).
  pose proof IJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PFROM_STK <= a < spZ regs) ->
            aview segs (w_H W) mem2 a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; rewrite (HK2 a Ha) by lia; apply KE1; [exact Ha | exact Hn]).
  (* the frame across the call *)
  assert (BY2 : forall i, 0 <= i < 48 -> mem2 (wa (spZ regs + -48 + i)) = m1 (wa (spZ regs + -48 + i))).
  { intros i Hi. unfold wa. apply (decode_byte_eq (w_H W) (w_H W) m1 mem2 (spZ regs + -48 + i)).
    - apply Hpres1. lia.
    - apply Hpres2. lia.
    - apply HK2; lia. }
  pose proof (decode_rw_cells_eq m1 mem2 _ _ FR ltac:(intros i Hi; apply BY2; cbn in Hi; lia)) as FR2.
  (* the registers after the call *)
  assert (Q2 : forall r, acallee_saved r -> YKW.getr regs2 (Z_to_bv 5 r) = YKW.getr RA (Z_to_bv 5 r))
    by exact HP2.
  assert (P2 : forall r, r = 3 \/ r = 4 \/ 21 <= r <= 27 -> YKW.getr regs2 (Z_to_bv 5 r) = YKW.getr regs (Z_to_bv 5 r))
    by (intros r Hr; rewrite (Q2 r ltac:(unfold acallee_saved; lia)); apply P1; exact Hr).
  pose proof (pfw_strcmpZ_unsigned xs CCW.NAME_C24 NX ltac:(cbn; intuition discriminate)) as CU1.
  assert (E8 : YKW.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 x)
    by (rewrite (Q2 8 ltac:(unfold acallee_saved; lia)); exact G8).
  assert (E2 : YKW.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -48))
    by (rewrite (Q2 2 ltac:(unfold acallee_saved; lia)); exact G2).
  (* the reads of turn 1 at the first call's return *)
  pose proof (decode_zshadow_rd B lyc Sc W mem2 md2 TRANS_PERS (TRANS_PERS + 48) (TRANS_PERS + 32) HAR2
                ltac:(reflexivity) ltac:(lia) ltac:(lia) ZPS) as VS1.
  assert (BS1 : bytes_at rsegs mem2 (PCB.shadow_addr (TRANS_PERS + 32)) [Z_to_bv 8 0])
    by (apply (pfw_bytes1 W mem2); [exact VS1 | unfold PCB.shadow_addr, PCB.ASAN_K, TRANS_PERS; lia]).
  assert (BP1 : bytes_at rsegs mem2 (TRANS_PERS + 32) (le8 (wa (PFW_NAME 1)))).
  { apply (pfw_bytes_rom W mem2); [|vm_compute; reflexivity | unfold TRANS_PERS; lia | rewrite length_le8; unfold TRANS_PERS; lia].
    intros i Hi. rewrite length_le8 in Hi. rewrite KE2 by (unfold TRANS_PERS; lia). apply HROM.
    apply (pfw_ro_rd TRANS_PERS 48); [pfw_in | lia]. }
  (* ---- the run from the first call's return ---- *)
  eapply (@decode_run fx W regs2 mem2 md2 PFW_RET).
  { unfold LCW.ms_of_regs.
    eapply pfw_run2_F.
    - rewrite (Q2 9 ltac:(unfold acallee_saved; lia)). exact G9.
    - rewrite (Q2 18 ltac:(unfold acallee_saved; lia)). exact G18.
    - rewrite (Q2 19 ltac:(unfold acallee_saved; lia)). exact G19.
    - rewrite (Q2 20 ltac:(unfold acallee_saved; lia)). exact G20.
    - rewrite E2, unsigned_lit by lia. lia.
    - rewrite E2, unsigned_lit by lia. lia.
    - rewrite E2, unsigned_lit by lia. exact FR2.
    - exact BS1.
    - exact BP1.
    - rewrite E2, unsigned_lit by lia.
      apply (decode_rng_vis W); [lia | lia |]. intros i Hi.
      destruct (Hpres2 (spZ regs + -48 + i) ltac:(lia)) as [Hh _]. exact Hh.
    - apply (decode_rng_vis W); [unfold PCB.shadow_addr, PCB.ASAN_K, TRANS_PERS; lia
                            | unfold PCB.shadow_addr, PCB.ASAN_K, TRANS_PERS; lia |].
      intros i Hi. replace (PCB.shadow_addr (TRANS_PERS + 32) + i) with (FCells.shadow_addr (TRANS_PERS + 32)) by lia.
      exact (pfw_aview_vis W mem2 _ 0 VS1).
    - apply (decode_rng_vis W); [unfold TRANS_PERS; lia | unfold TRANS_PERS; lia |].
      intros i Hi. apply (pfw_ro_vis W memc _ HROM). apply (pfw_ro_rd TRANS_PERS 48); [pfw_in | lia]. }
  pose proof (ret_ok_stmt_YK0s (YKW.getr regs (Z_to_bv 5 1)) Hra) as ERA.
  intros ms1 msB mdB HPB EQVB _ SBMB.
  destruct HPB as [(Hr0 & a1' & ->) | (Hr0 & ->)].
  - (* strcmp(x, "CNTRL|24") = 0: the return with a0 = personalities *)
    unfold pfw_ret_ms in EQVB. destruct (decode_eqv_mkst _ _ _ _ EQVB) as (RB & -> & HXB). clear EQVB.
    assert (Es : xs = CCW.NAME_C24) by (apply CU1; rewrite <- HV2; exact Hr0).
    assert (IJ3 : @ajournal rc YE2k.tfib_sink_head tfibsegs B PFROM_STK (spZ regs) [] lyc Sc W memc mdc []
                    lyc Sc W mem2 mdB 0).
    { apply (@ajournal_exec rc YE2k.tfib_sink_head tfibsegs B LAWS decode_segs_low PFROM_STK (spZ regs) []
               lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 mem2 mdB (fun _ => False) IJ2);
        [intros x0 _; reflexivity | apply YK1b.mem_grows_refl | intros x0 _; reflexivity | exact SBMB
        | intros a Ha; destruct Ha]. }
    apply SRr_ret. rewrite ERA.
    apply (pfw_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs tb mem2 mdB RB
             LAWS MTL HJ IJ3 Hwlo Hwhi).
    + apply pfw_pres_groups.
      * transitivity (Z_to_bv 64 (bv_unsigned (YKW.getr regs2 (Z_to_bv 5 2)) + 48)); [pfw_reg HXB|].
        rewrite E2, unsigned_lit by lia. replace (spZ regs + -48 + 48) with (spZ regs) by lia.
        unfold spZ. apply Z_to_bv_bv_unsigned.
      * intros r Hr. transitivity (YKW.getr regs2 (Z_to_bv 5 r)); [pfw_cases3 r; pfw_reg HXB | apply P2; exact Hr].
      * intros r Hr. pfw_cases8 r; pfw_reg HXB.
    + transitivity (Z_to_bv 64 TRANS_PERS); [pfw_reg HXB|].
      rewrite (pfw_res tb sx rest Htb NX). fold xs. rewrite Es.
      destruct (list_eq_dec Z.eq_dec CCW.NAME_C24 CCW.NAME_C24) as [_|C]; [reflexivity | exfalso; exact (C eq_refl)].
  - (* strcmp(x, "CNTRL|24") <> 0: turn 1, strcmp(x, "MAINUNIT") *)
    unfold pfw_call_ms in EQVB. destruct (decode_eqv_mkst _ _ _ _ EQVB) as (RB & -> & HXB). clear EQVB.
    assert (Ns : xs <> CCW.NAME_C24) by (intros C; apply Hr0; rewrite HV2; apply CU1; exact C).
    assert (IJ2B : @ajournal rc YE2k.tfib_sink_head tfibsegs B PFROM_STK (spZ regs) [] lyc Sc W memc mdc []
                     lyc Sc W mem2 mdB 0).
    { apply (@ajournal_exec rc YE2k.tfib_sink_head tfibsegs B LAWS decode_segs_low PFROM_STK (spZ regs) []
               lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 mem2 mdB (fun _ => False) IJ2);
        [intros x0 _; reflexivity | apply YK1b.mem_grows_refl | intros x0 _; reflexivity | exact SBMB
        | intros a Ha; destruct Ha]. }
    assert (H1' : YKW.getr RB (Z_to_bv 5 1) = Z_to_bv 64 PFW_RET) by pfw_reg HXB.
    assert (H2' : YKW.getr RB (Z_to_bv 5 2) = YKW.getr regs2 (Z_to_bv 5 2)) by pfw_reg HXB.
    assert (H3' : YKW.getr RB (Z_to_bv 5 3) = YKW.getr regs2 (Z_to_bv 5 3)) by pfw_reg HXB.
    assert (H4' : YKW.getr RB (Z_to_bv 5 4) = YKW.getr regs2 (Z_to_bv 5 4)) by pfw_reg HXB.
    assert (H10' : YKW.getr RB (Z_to_bv 5 10) = YKW.getr regs2 (Z_to_bv 5 8)) by pfw_reg HXB.
    assert (H11' : YKW.getr RB (Z_to_bv 5 11) = Z_to_bv 64 TRANS_PNAME1) by pfw_reg HXB.
    assert (H18' : YKW.getr RB (Z_to_bv 5 18) = Z_to_bv 64 1) by pfw_reg HXB.
    assert (H20' : YKW.getr RB (Z_to_bv 5 20) = Z_to_bv 64 (TRANS_PERS + 24)) by pfw_reg HXB.
    assert (P3 : forall r, r = 3 \/ r = 4 \/ 21 <= r <= 27 ->
              YKW.getr RB (Z_to_bv 5 r) = YKW.getr regs (Z_to_bv 5 r)).
    { intros r Hr. transitivity (YKW.getr regs2 (Z_to_bv 5 r)); [pfw_cases3 r; pfw_reg HXB | apply P2; exact Hr]. }
    assert (GSP2 : spZ RB = spZ regs + -48).
    { change (spZ RB) with (bv_unsigned (YKW.getr RB (Z_to_bv 5 2))).
      rewrite H2', E2, unsigned_lit by lia. reflexivity. }
    assert (CX2 : pfw_cstr_at W mem2 x xs)
      by (apply (pfw_cstr_kept W memc mem2 x xs (spZ regs - PFROM_STK) (spZ regs) CX0 KE2); lia).
    assert (CN12 : pfw_cstr_at W mem2 TRANS_PNAME1 CCW.NAME_PC)
      by (apply (pfw_cstr_kept W memc mem2 TRANS_PNAME1 CCW.NAME_PC (spZ regs - PFROM_STK) (spZ regs) CN1 KE2);
          rewrite ?pfw_len_pc; unfold TRANS_PNAME1; lia).
    assert (RX2 : decode_rd_ok W mem2 x (Z.of_nat (length xs) + 1)).
    { apply (trans_rd_ok_view W W memc mem2 x _ RX0).
      - intros a Ha. apply KE2; lia.
      - intros s Hs. apply KE2; unfold kLowMemEnd, kHighShadowEnd in Hs; lia. }
    assert (RN12 : decode_rd_ok W mem2 TRANS_PNAME1 (Z.of_nat (length CCW.NAME_PC) + 1)).
    { apply (trans_rd_ok_view W W memc mem2 _ _ RN1).
      - intros a Ha. rewrite pfw_len_pc in Ha. apply KE2; unfold TRANS_PNAME1 in Ha; lia.
      - intros s Hs. apply KE2; unfold kLowMemEnd, kHighShadowEnd in Hs; lia. }
    eapply SRr_bind.
    { apply (pfw_strcmp_cstr_at B LAWS PFW_STRCMP (STRCMP fx) W RB mem2 PFROM_STK (spZ regs) [] lyc Sc W
               memc mdc [] lyc Sc mdB 0 x TRANS_PNAME1 xs CCW.NAME_PC (-48) PFW_RET IJ2B).
      - rewrite H10'. exact E8.
      - exact H11'.
      - lia.
      - unfold TRANS_PNAME1; lia.
      - exact GSP2.
      - reflexivity.
      - lia.
      - lia.
      - rewrite H3', (Q2 3 ltac:(unfold acallee_saved; lia)), G3. exact Hgp.
      - rewrite H4', (Q2 4 ltac:(unfold acallee_saved; lia)), G4. exact Htp.
      - exact H1'.
      - unfold PFW_RET; pfw_lits; lia.
      - apply YK0s.ret_ok_even. vm_compute. reflexivity.
      - rewrite pfw_len_pc. lia.
      - exact CX2.
      - exact CN12.
      - exact RX2.
      - exact RN12.
      - intros a Ha. lia.
      - intros a Ha. rewrite pfw_len_pc in Ha. unfold TRANS_PNAME1 in Ha. lia. }
    cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & IJ3 & HP3 & SB3 & HV3 & HK3 & HPR3).
    pose proof IJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
    assert (BY3 : forall i, 0 <= i < 48 -> mem3 (wa (spZ regs + -48 + i)) = mem2 (wa (spZ regs + -48 + i))).
    { intros i Hi. unfold wa. apply (decode_byte_eq (w_H W) (w_H W) mem2 mem3 (spZ regs + -48 + i)).
      - apply Hpres2. lia.
      - apply Hpres3. lia.
      - apply HK3; lia. }
    pose proof (decode_rw_cells_eq mem2 mem3 _ _ FR2 ltac:(intros i Hi; apply BY3; cbn in Hi; lia)) as FR3.
    assert (Q3 : forall r, acallee_saved r -> YKW.getr regs3 (Z_to_bv 5 r) = YKW.getr RB (Z_to_bv 5 r))
      by exact HP3.
    assert (E2' : YKW.getr regs3 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -48))
      by (rewrite (Q3 2 ltac:(unfold acallee_saved; lia)), H2'; exact E2).
    pose proof (pfw_strcmpZ_unsigned xs CCW.NAME_PC NX ltac:(cbn; intuition discriminate)) as CU2.
    (* ---- the run from the second call's return ---- *)
    eapply (@decode_run fx W regs3 mem3 md3 PFW_RET).
    { unfold LCW.ms_of_regs.
      eapply pfw_run3_F.
      - rewrite (Q3 18 ltac:(unfold acallee_saved; lia)). exact H18'.
      - rewrite (Q3 20 ltac:(unfold acallee_saved; lia)). exact H20'.
      - rewrite E2', unsigned_lit by lia. lia.
      - rewrite E2', unsigned_lit by lia. lia.
      - rewrite E2', unsigned_lit by lia. exact FR3.
      - rewrite E2', unsigned_lit by lia.
        apply (decode_rng_vis W); [lia | lia |]. intros i Hi.
        destruct (Hpres3 (spZ regs + -48 + i) ltac:(lia)) as [Hh _]. exact Hh. }
    intros ms2 msC mdC (a1'' & ->) EQVC _ SBMC.
    unfold pfw_ret_ms in EQVC. destruct (decode_eqv_mkst _ _ _ _ EQVC) as (RC & -> & HXC). clear EQVC.
    assert (IJ4 : @ajournal rc YE2k.tfib_sink_head tfibsegs B PFROM_STK (spZ regs) [] lyc Sc W memc mdc []
                    lyc Sc W mem3 mdC 0).
    { apply (@ajournal_exec rc YE2k.tfib_sink_head tfibsegs B LAWS decode_segs_low PFROM_STK (spZ regs) []
               lyc Sc W memc mdc [] lyc Sc W mem3 md3 0 mem3 mdC (fun _ => False) IJ3);
        [intros x0 _; reflexivity | apply YK1b.mem_grows_refl | intros x0 _; reflexivity | exact SBMC
        | intros a Ha; destruct Ha]. }
    apply SRr_ret. rewrite ERA.
    apply (pfw_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs tb mem3 mdC RC
             LAWS MTL HJ IJ4 Hwlo Hwhi).
    + apply pfw_pres_groups.
      * transitivity (Z_to_bv 64 (bv_unsigned (YKW.getr regs3 (Z_to_bv 5 2)) + 48)); [pfw_reg HXC|].
        rewrite E2', unsigned_lit by lia. replace (spZ regs + -48 + 48) with (spZ regs) by lia.
        unfold spZ. apply Z_to_bv_bv_unsigned.
      * intros r Hr. transitivity (YKW.getr regs3 (Z_to_bv 5 r)); [pfw_cases3 r; pfw_reg HXC|].
        rewrite (Q3 r ltac:(unfold acallee_saved; lia)). apply P3. exact Hr.
      * intros r Hr. pfw_cases8 r; pfw_reg HXC.
    + transitivity (Z_to_bv 64 (if bv_unsigned (YKW.getr regs3 (Z_to_bv 5 10)) =? 0 then TRANS_PERS + 24 else 0));
        [pfw_reg HXC|].
      rewrite HV3, (pfw_res tb sx rest Htb NX). fold xs.
      destruct (list_eq_dec Z.eq_dec xs CCW.NAME_C24) as [C|_]; [exfalso; exact (Ns C)|].
      destruct (list_eq_dec Z.eq_dec xs CCW.NAME_PC) as [E|E];
        destruct (Z.eqb_spec (bv_unsigned (w64 (pfw_strcmpZ xs CCW.NAME_PC))) 0) as [U|U];
        first [reflexivity | exfalso; apply U; apply CU2; exact E | exfalso; apply E; apply CU2; exact U].
Qed.
End walk.

Theorem transport_diginet_personality_from_name_cg_holds :
  forall fx rc B MT, @transport_diginet_personality_from_name_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@pfw_holds fx rc B MT). Qed.
