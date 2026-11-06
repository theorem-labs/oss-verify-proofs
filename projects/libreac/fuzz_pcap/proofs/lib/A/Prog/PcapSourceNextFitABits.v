(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: three image-free facts for the fit
   phase (PcapSourceNextFitA.v, NP_fit 0x81b40 .. NP_ts 0x81ce4), stated by that phase's lane.

   - fa_ts_noswap: a timestamp word as 0x81b40..0x81bb8 builds it from four header bytes, not swapped
     (the bytes a0 .. a3 shifted by 0, 8, 16, 24, all in 64 bits): PSN.w32le x0 x1 x2 x3.
   - fa_ts_swap: the same word byte-swapped (ps->sw <> 0) from that unswapped word RAW, its low 32
     bits: PSN.w32le x3 x2 x1 x0.
   - fa_mm_list: the list effect of __asan_memmove(buf + 12, buf + 16, incl - 16) (0x81cdc), stated
     pointwise on the buffer before (old) and after (new): the first n bytes after the call are the
     tagged record of PSN.rec_bytes (bytes 0..11, then 16..n-1 moved down by 4, then the last 4 kept).

   The file names no image and no address: it Requires only lib/Reusable (YZ00, YP0m, YP0e),
   lib/Prog/pcap_source_struct_next.v (for PSN.w32le), which PcapSourceNextSpec.v Requires too, and
   the image-free lib/A/Prog/PcapSourceNextWords.v.

   TAKEN FROM: all the word arithmetic (nx_asm_lo64, nx_asm_sw64, nx_wrap64) and the two list
   lemmas (nx_nth_firstn_lt, nx_nth_skipn_add) come from PcapSourceNextWords.v, which is their one
   home; this file holds no copy of them. fa_ts_noswap and fa_ts_swap are new as statements (the
   U / sv form the FitA walk needs) and are four lines of plumbing over nx_asm_lo64 / nx_asm_sw64.
   fa_mm_list is new, no donor: searched 2026-10-29 03:12Z with proof-index w32le (index v5 of
   01:50Z over main f4cc67298b, ossv/recipes 5121fb8693, ossv/candidates ee89628c99,
   release/pau-projects-recipes b6a0088adc and an earlier delivery) and git grep of
   origin/ossv/recipes; the nearest released donor, mm_rec (lib/Prog/pcap_source_next_lib.v:577),
   states the same list on upd_bytes over list byte with `length B = n`, not pointwise over list Z. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextWords.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the two timestamp words (0x81b40..0x81bb8) ---- *)

Lemma fa_ts_noswap : forall E a0 a1 a2 a3 x0 x1 x2 x3,
  U E a0 = x0 -> U E a1 = x1 -> U E a2 = x2 -> U E a3 = x3 ->
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL a1 (SLit 8)) a0)
                   (SAlu ALU_OR (SAlu ALU_SLL a2 (SLit 16)) (SAlu ALU_SLL a3 (SLit 24))))
    = PSN.w32le x0 x1 x2 x3.
Proof.
  intros E a0 a1 a2 a3 x0 x1 x2 x3 E0 E1 E2 E3 H0 H1 H2 H3.
  unfold U at 1. cbn [sv_denot].
  rewrite (denot_lit_U E a0), (denot_lit_U E a1), (denot_lit_U E a2), (denot_lit_U E a3), E0, E1, E2, E3.
  rewrite (nx_asm_lo64 x0 x1 x2 x3 H0 H1 H2 H3), Z_to_bv_unsigned, nx_wrap64.
  apply Z.mod_small. unfold PSN.w32le. lia.
Qed.

Lemma fa_ts_swap : forall E a0 a1 a2 a3 x0 x1 x2 x3,
  U E a0 = x0 -> U E a1 = x1 -> U E a2 = x2 -> U E a3 = x3 ->
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  U E (SAlu ALU_OR
         (SAlu ALU_OR (SAlu ALU_SLL a0 (SLit 24))
                      (SAlu ALU_SLL
                         (SAlu ALU_AND
                            (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL a1 (SLit 8)) a0)
                                         (SAlu ALU_OR (SAlu ALU_SLL a2 (SLit 16)) (SAlu ALU_SLL a3 (SLit 24))))
                            (SLit 65280))
                         (SLit 8)))
         (SAlu ALU_OR (SAlu ALU_SLL a2 (SLit 8))
                      (SAluw ALU_SRL
                         (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL a1 (SLit 8)) a0)
                                      (SAlu ALU_OR (SAlu ALU_SLL a2 (SLit 16)) (SAlu ALU_SLL a3 (SLit 24))))
                         (SLit 24))))
    mod 2 ^ 32 = PSN.w32le x3 x2 x1 x0.
Proof.
  intros E a0 a1 a2 a3 x0 x1 x2 x3 E0 E1 E2 E3 H0 H1 H2 H3.
  unfold U at 1. cbn [sv_denot].
  rewrite (denot_lit_U E a0), (denot_lit_U E a1), (denot_lit_U E a2), (denot_lit_U E a3), E0, E1, E2, E3.
  rewrite (nx_asm_lo64 x0 x1 x2 x3 H0 H1 H2 H3).
  rewrite (nx_asm_sw64 x0 x1 x2 x3 H0 H1 H2 H3 _ eq_refl), Z_to_bv_unsigned, nx_wrap64.
  rewrite (Z.mod_small (PSN.w32le x3 x2 x1 x0)) by (unfold PSN.w32le; lia).
  apply Z.mod_small. unfold PSN.w32le. lia.
Qed.

(* ---- the memmove of the VLAN tag (0x81cdc) on the buffer's bytes ---- *)

Lemma fa_mm_list : forall (old new : list Z) (n : nat),
  (18 <= n)%nat -> (n <= length old)%nat -> length new = length old ->
  (forall i, (i < length new)%nat ->
     nth i new 0 = if ((12 <=? i) && (i <? n - 4))%nat then nth (i + 4) old 0 else nth i old 0) ->
  firstn n new = firstn 12 (firstn n old)
                 ++ firstn (n - 16) (skipn 16 (firstn n old))
                 ++ skipn (n - 4) (firstn n old).
Proof.
  intros old new n Hn Hno Hlen Hnth.
  assert (LO : length (firstn n old) = n) by (rewrite length_firstn; apply Nat.min_l; exact Hno).
  assert (LN : length (firstn n new) = n) by (rewrite length_firstn; apply Nat.min_l; lia).
  assert (L12 : length (firstn 12 (firstn n old)) = 12%nat) by (rewrite length_firstn, LO; apply Nat.min_l; lia).
  assert (LM : length (firstn (n - 16) (skipn 16 (firstn n old))) = (n - 16)%nat)
    by (rewrite length_firstn, length_skipn, LO; apply Nat.min_id).
  assert (LT : length (skipn (n - 4) (firstn n old)) = 4%nat) by (rewrite length_skipn, LO; lia).
  apply nth_ext with (d := 0) (d' := 0).
  { rewrite LN, !length_app, L12, LM, LT. lia. }
  intros i Hi. rewrite LN in Hi.
  rewrite (nx_nth_firstn_lt _ new i n 0 Hi), (Hnth i) by lia.
  destruct (Nat.leb_spec 12 i) as [H12|H12]; cbn [andb].
  - rewrite app_nth2 by (rewrite L12; exact H12). rewrite L12.
    destruct (Nat.ltb_spec i (n - 4)) as [H4|H4]; cbn [andb].
    + rewrite app_nth1 by (rewrite LM; lia).
      rewrite (nx_nth_firstn_lt _ _ (i - 12) (n - 16) 0) by lia.
      rewrite nx_nth_skipn_add, nx_nth_firstn_lt by lia.
      f_equal. lia.
    + rewrite app_nth2 by (rewrite LM; lia). rewrite LM.
      rewrite nx_nth_skipn_add, nx_nth_firstn_lt by lia.
      f_equal. lia.
  - rewrite app_nth1 by (rewrite L12; exact H12).
    rewrite !nx_nth_firstn_lt by lia. reflexivity.
Qed.
