(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths and module names changed; 3307 of its 3394 lines of code are new or changed and 718 lines of the source are left out. *)
(* libreac/fuzz_boxreg, image A (fuzz_boxreg.asan): the find case (op & 3 = 2) of LLVMFuzzerTestOneInput, the walk
   0x80354 .. 0x80ab4 (fuzz_boxreg.c:363-384) in the PA engine, from the cut T (GI_T 2 i) to the join K (GI_K i).
   Theorem gb_case2 : forall i, gb_from B MT POST (GI_K B MT i) -> gb_from B MT POST (GI_T B MT 2 i).
   The cuts, gb_from and gb_base are BoxLxDefs.v's; the seat facts and the keep lemmas are BoxLxSeat.v's.

   Shape of the walk. The head (read_mac inlined) runs from the seat c2h_ss kk, kk = min 6 (n - pos) input bytes
   known at the cursor (one engine run per kk, kk = 0 .. 6), to 0x80614 (GP_F):
   - op & 4 <> 0 (0x80358 taken): the six-byte loop 0x80430 .. 0x8047c; the loop's exit test on the bytes left is the
     one data branch the engine leaves open when kk < 6 (refuted on its "bytes left <> 0" side by n - pos = kk);
   - op & 4 = 0: __asan_memcpy (mac, read_mac.base, 5) at 0x80370 (aj_intrin_at with AMEMCPY; the five bytes are
     read_mac.base's read-only bytes 00 40 ab 00 00, HRMB; its shadow from HGLOB / HISV; mac and the global are apart
     by AR's client/image law, c2_frame_rom_disj), then mac[5] = one input byte (0x80374 .. 0x80610).
   At 0x80614 c2_fin rebuilds the facts c2_FI the tail needs (c2_mkFI: what the head keeps, c2_hkeep), and c2_tail
   walks reac_boxreg_find (r, mac) at 0x8061c (TFIND) and the checks 0x80624 .. 0x8068c (bcmp at 0x80660 and 0x80678,
   ABCMP) to K with bs' = bs and ren = -1 (Pau's c2_kept, lib/Prog/LLVMFuzzerTestOneInput_case2.v).

   The branches of the phase that lead to a report or abort body (none is stepped into):
   pc       target                           test                              refuted by
   0x8039c  0x80dec -> 0x80df0 -> 0x80fe8    shadow of the input byte (A)      the input entry of c2h_SH (c2h_sh_gen)
   0x80454  0x80480 -> 0x80484 -> 0x80f94    shadow of the input byte (B)      the input entry of c2h_SH (c2h_sh)
   0x80634  0x80d38 -> 0x80d3c -> 0x80fa8    shadow of r->n (r + 280)          the shadow byte 0 of c2_rsh (c2_rsh_ok)
   0x80628  0x80f60                          idx < -1                          find_result (c2_find_range)
   0x80640  0x80f60                          idx >= r->n                       find_result (c2_find_range)
   0x80664  0x80f60                          bcmp (box[idx].mac, mac, 6) <> 0  c2_bcmp1 (box idx holds mac, c2_find_hit)
   0x80688  0x80f60                          bcmp (mac, ZERO, 6) = 0, idx<>-1  c2_bcmp0 (mac <> ZERO, c2_find_hit) *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC4b YC85 BoxFrame BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit ReacBoxregFind.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs BoxLxSeat.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg reac_boxreg_find_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- Pau's model of the find case (address-free) ---- *)
Lemma c2_find_range : forall bs M z, Boxreg.boxreg_B1 bs -> reac_boxreg_find_c.find_result bs M z ->
  -1 <= z < Boxreg.bx_n bs.
Proof.
intros bs M z HB1 FR. unfold Boxreg.boxreg_B1 in HB1.
destruct FR as [[_ ->] | [[_ (Hz & _ & _)] | (_ & -> & _)]]; lia.
Qed.
Lemma c2_find_hit : forall bs M z, reac_boxreg_find_c.find_result bs M z -> 0 <= z ->
  Boxreg.bx_mac bs z = M /\ M <> Boxreg.zero6.
Proof.
intros bs M z FR Hz.
destruct FR as [[_ ->] | [[NZ (_ & Hm & _)] | (_ & -> & _)]]; [lia | split; [exact Hm | exact NZ] | lia].
Qed.
Lemma c2_find_nz : forall bs M z, reac_boxreg_find_c.find_result bs M z -> z <> -1 -> M <> Boxreg.zero6.
Proof.
intros bs M z FR Hz.
destruct FR as [[_ E] | [[NZ _] | (_ & E & _)]]; [lia | exact NZ | lia].
Qed.
(* A MAC of six bytes that is not the zero MAC has a byte that is not 0. *)
Lemma c2_nz_byte : forall M : list byte, length M = 6%nat -> M <> Boxreg.zero6 ->
  exists j, (j < 6)%nat /\ bv_unsigned (nth j M (Z_to_bv 8 0)) <> 0.
Proof.
intros M HL HN.
destruct M as [|m0 [|m1 [|m2 [|m3 [|m4 [|m5 [|m6 M]]]]]]]; cbn [length] in HL; try lia.
destruct (Z.eq_dec (bv_unsigned m0) 0) as [E0|E0]; [|exists 0%nat; split; [lia | exact E0]].
destruct (Z.eq_dec (bv_unsigned m1) 0) as [E1|E1]; [|exists 1%nat; split; [lia | exact E1]].
destruct (Z.eq_dec (bv_unsigned m2) 0) as [E2|E2]; [|exists 2%nat; split; [lia | exact E2]].
destruct (Z.eq_dec (bv_unsigned m3) 0) as [E3|E3]; [|exists 3%nat; split; [lia | exact E3]].
destruct (Z.eq_dec (bv_unsigned m4) 0) as [E4|E4]; [|exists 4%nat; split; [lia | exact E4]].
destruct (Z.eq_dec (bv_unsigned m5) 0) as [E5|E5]; [|exists 5%nat; split; [lia | exact E5]].
exfalso. apply HN. unfold Boxreg.zero6. cbn [repeat].
assert (Z0 : forall b : byte, bv_unsigned b = 0 -> b = Z_to_bv 8 0)
  by (intros b Hb; apply bv_eq; rewrite Hb; reflexivity).
rewrite (Z0 m0 E0), (Z0 m1 E1), (Z0 m2 E2), (Z0 m3 E3), (Z0 m4 E4), (Z0 m5 E5). reflexivity.
Qed.
(* Box z's MAC, byte j, is byte 56 z + j of the table. *)
Lemma c2_mac_nth : forall (bs : list byte) z j, 0 <= z -> (j < 6)%nat ->
  nth j (Boxreg.bx_mac bs z) (Z_to_bv 8 0) = nth (Z.to_nat (56 * z + Z.of_nat j)) bs (Z_to_bv 8 0).
Proof.
intros bs z j Hz Hj. unfold Boxreg.bx_mac, Boxreg.bsub. change (Z.to_nat 6) with 6%nat.
rewrite nth_firstn. destruct (j <? 6)%nat eqn:E; [|apply Nat.ltb_ge in E; lia].
rewrite nth_skipn. f_equal. lia.
Qed.

Local Ltac zbool :=
repeat match goal with
| H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
| H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
end.

(* ---- the symbolic state of the phase ---- *)
(* The atoms: 0 .. 31 the registers at the seat; then the phase's own values (Ereg's extra list, atom 32 + j):
   32 the input cursor c_p + pos, 33 the bytes left c_n - pos, 34 the turn i, 35 the shadow address of r + 8,
   36 the shadow address of r + 280, 37 r->n = bx_n bs, 38 the frame F, 39 .. 44 the input bytes at the cursor
   (head) or the six MAC bytes (tail); 240 .. 511 the image. A call's junk atoms start at 45. *)
Definition C2_SB : Z := 0x7fff8000.
Definition c2_Bx : sv := SOff 18 0.
Definition c2_span : Z * Z := (C2_SB, C2_SB + 2 ^ 44 - 1).
(* The spill slots of the machine frame at s1 (atom 9). *)
Definition c2_slot_chunks (cur rem : sv) : list YP09.chunk :=
  [ YP09.mkChunk 16 (CVal 8 (SLit 3)); YP09.mkChunk 24 (CVal 8 (SOff 38 0)); YP09.mkChunk 32 (CVal 8 (SOff 38 76));
    YP09.mkChunk 40 (CVal 8 (SOff 38 0)); YP09.mkChunk 56 (CVal 8 (SOff 35 0)); YP09.mkChunk 64 (CVal 8 (SOff 20 280));
    YP09.mkChunk 80 (CVal 8 (SOff 25 0)); YP09.mkChunk 96 (CVal 8 (SOff 36 0)); YP09.mkChunk 104 (CVal 8 (SOff 34 0));
    YP09.mkChunk 112 (CVal 8 (SOff 38 32)); YP09.mkChunk 120 (CVal 8 (SOff 38 64)); YP09.mkChunk 128 (CVal 8 (SOff 38 0));
    YP09.mkChunk 136 (CVal 8 cur); YP09.mkChunk 144 (CVal 8 rem) ].
Definition c2_spill (cur rem : sv) (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x98 wlo whi (c2_slot_chunks cur rem).
(* r->n (4 bytes at r + 280) and its shadow byte. *)
Definition c2_rn : YP09.region := YP09.mkRegion (Some 20%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 37 0))].
Definition c2_rsh : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
(* k bytes of chunks, atom 39 + j at offset o + j. *)
Definition c2_bytes (o : Z) (k : nat) : list YP09.chunk :=
  map (fun j => YP09.mkChunk (o + Z.of_nat j) (CVal 1 (SOff (39 + j) 0))) (seq 0 k).
(* The input bytes at the cursor. *)
Definition c2_inb (k : nat) : YP09.region := YP09.mkRegion (Some 32%nat) 0 (Z.of_nat k) 0 0 (c2_bytes 0 k).
(* The frame F (atom 38); the head may write mac[0 .. 5]. *)
Definition c2_frame (cs : list YP09.chunk) (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 38%nat) 0 512 wlo whi cs.

(* The head's state at 0x80354 with k input bytes known at the cursor. *)
Definition c2h_regions (k : nat) : YP09.smem :=
  [c2_spill (SOff 32 0) (SOff 33 0) 0x88 0x98; c2_frame [] 32 38; c2_rn; c2_rsh] ++
  (if (k =? 0)%nat then [] else [c2_inb k]).
Definition c2_rem_fact (k : nat) : afact := mkAF (Z.of_nat k) (if (k <? 6)%nat then Z.of_nat k else 2 ^ 26) 0.
Definition c2h_G (k : nat) : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF C2_SB C2_SB 0); (32%nat, mkAF 4096 140737479966720 0);
           (38%nat, mkAF 4096 140737479966720 6); (33%nat, c2_rem_fact k); (37%nat, mkAF 0 5 0)] [] [].
Definition c2h_SH (k : nat) : list shent := [mkSHE 38 32 38; mkSHE 32 0 (Z.of_nat k)].
Definition c2h_ss (k : nat) : sstate := mkSS (GP_T 2) sr_atoms (c2h_regions k) None (c2h_G k).

(* The tail's state at 0x80614 (offset 0x6c8): the MAC's six bytes in the frame, nothing writable. *)
Definition GP_F : Z := 0x6c8.
Definition c2t_regions : YP09.smem := [c2_spill (SOff 32 0) (SOff 33 0) 0 0; c2_frame (c2_bytes 32 6) 0 0; c2_rn; c2_rsh].
Definition c2t_G : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF C2_SB C2_SB 0); (37%nat, mkAF 0 5 0)] [] [].
Definition c2t_ss : sstate := mkSS GP_F sr_atoms c2t_regions None c2t_G.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.

Section d.
Variables (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS).
Variables (i r pos op : Z) (bs : list byte).
Hypothesis HB : gb_base B MT cx.
Hypothesis HFR : frames S3 = [(GB_CID, fp)].
Hypothesis HBLK : gblk1 B cx ly3 S3 r.
Hypothesis HINV : Boxreg.boxreg_inv bs.

(* The environment of the phase: the seat's registers, then the phase's values. *)
Definition c2_inbyte (j : nat) : Z :=
  if (Z.to_nat pos + j <? length (c_pl cx))%nat
  then bv_unsigned (nth (Z.to_nat pos + j) (c_pl cx) (Z_to_bv 8 0)) else 0.
Definition c2_ex (bytes : list Z) : list word :=
  map w64 ([c_p cx + pos; c_n cx - pos; i; shadow_of_addr SHADOW_OFF (r + 8); shadow_of_addr SHADOW_OFF (r + 280);
            Boxreg.bx_n bs; gF cx fp] ++ bytes).
Definition c2h_bytes : list Z := map c2_inbyte (seq 0 6).
Lemma c2_cn : 0 <= c_n cx < 2 ^ 26.
Proof.
pose proof HB as (_ & _ & _ & Hinp & _). unfold c_n in *.
destruct Hinp as [(H0 & _) | (H0 & _)]; lia.
Qed.

(* ---- the geometry of a point of the phase ---- *)
Section e.
Variable ms3 : machine_state.
Variable md3 : Model.
Hypothesis HJ : ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HREG : greg B ly3 S3 W3 ms3 r bs.

Lemma c2_rblk : In (r, REG_SIZE) (ablocks B ly3 S3).
Proof. unfold gblk1 in HBLK. rewrite HBLK. apply in_or_app. right. left. reflexivity. Qed.

(* The blocks the phase meets (the input and r) and the frame, from AR's separation law. *)
Lemma c2_geo :
  (spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
   spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0) /\
  (4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512 /\ gF cx fp mod 64 = 0 /\
   gSH cx fp = SHADOW_OFF + gF cx fp / 8) /\
  (r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ in_app r 288) /\
  (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r) /\
  ((c_n cx = 0 /\ c_p cx = GB_EMPTY) \/
   (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ 4096 <= c_p cx /\
    c_p cx + c_n cx <= alloc_ceiling /\ in_app (c_p cx) (c_n cx) /\
    (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx) /\
    (c_p cx + c_n cx <= r \/ r + 288 <= c_p cx))).
Proof.
pose proof (gb_sp_facts B MT cx HB) as (Hs1 & Hs2 & Hs3 & Hs4).
pose proof (gb_sp1_al B MT cx HB) as Hs5.
pose proof (gb_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF1 & HF2 & HF3 & _ & HF5).
pose proof (gb_F_al B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as HF4.
pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
pose proof HJ as (HAR3 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 c2_rblk) as (Hr16 & Hr4096 & Hrc & Hria & _).
change (req_size REG_SIZE) with 288 in Hrc, Hria.
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR3) as [HSEP _].
rewrite HFR in HSEP. cbn [map fst snd] in HSEP. rewrite EF in HSEP.
change (fs_frame_bytes GB_CID) with 512 in HSEP.
unfold gblk1 in HBLK. rewrite HBLK, map_app in HSEP. cbn [map fst snd] in HSEP.
change (req_size REG_SIZE) with 288 in HSEP.
rewrite <- app_assoc in HSEP. cbn [app] in HSEP.
assert (DRF : r + 288 <= gF cx fp \/ gF cx fp + 512 <= r).
{ pose proof (pairwise_In zdisjoint _ (r, 288) (gF cx fp, 512)
    (map (fun b => (fst b, req_size (snd b))) (ablocks B (c_ly cx) (c_S cx)) ++ [(r, 288)]) [(gF cx fp, 512)]
    ltac:(rewrite <- app_assoc; reflexivity) HSEP ltac:(apply in_or_app; right; left; reflexivity)
    ltac:(left; reflexivity)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
split; [exact (conj Hs1 (conj Hs2 (conj Hs3 (conj Hs4 Hs5))))|].
split; [exact (conj HF1 (conj HF2 (conj HF3 (conj HF4 HF5))))|].
split; [exact (conj Hr16 (conj Hr4096 (conj Hrc Hria)))|]. split; [exact DRF|].
pose proof HB as (_ & _ & _ & Hinp & _).
destruct Hinp as [H0 | (Hn & Hin)]; [left; exact H0 | right].
assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; left; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpc & Hpia & _).
pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
assert (Hrqe : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
rewrite Hrqe in Hpc, Hpia.
assert (Hm : In (c_p cx, req_size (c_n cx)) (map (fun b => (fst b, req_size (snd b))) (ablocks B (c_ly cx) (c_S cx))))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (c_p cx, c_n cx)); exact Hin).
rewrite Hrqe in Hm.
assert (DPF : c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx).
{ pose proof (pairwise_In zdisjoint _ (c_p cx, c_n cx) (gF cx fp, 512)
    (map (fun b => (fst b, req_size (snd b))) (ablocks B (c_ly cx) (c_S cx)) ++ [(r, 288)]) [(gF cx fp, 512)]
    ltac:(rewrite <- app_assoc; reflexivity) HSEP ltac:(apply in_or_app; left; exact Hm)
    ltac:(left; reflexivity)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
assert (DPR : c_p cx + c_n cx <= r \/ r + 288 <= c_p cx).
{ pose proof (pairwise_In zdisjoint _ (c_p cx, c_n cx) (r, 288)
    (map (fun b => (fst b, req_size (snd b))) (ablocks B (c_ly cx) (c_S cx))) [(r, 288); (gF cx fp, 512)]
    eq_refl HSEP Hm ltac:(left; reflexivity)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
split; [lia|]. split; [exact Hin3|]. split; [exact Hp4096|]. split; [exact Hpc|].
split; [exact Hpia|]. split; [exact DPF | exact DPR].
Qed.


(* ---- the environment and the regions of a seat ---- *)
Definition c2_E (bytes : list Z) : env := Eimg (Ereg (ms_regs ms3) (c2_ex bytes)).
#[local] Notation M3 := (mrestrict (w_H W3) (ms_mem ms3)).

Lemma c2_ew_reg : forall bytes n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew (c2_E bytes) n = getr (ms_regs ms3) q.
Proof.
intros bytes n q Hn. pose proof (bv_unsigned_in_range 5 q) as Hq. change (bv_modulus 5) with 32 in Hq.
unfold c2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma c2_ew_ex : forall bytes j, (j < 200)%nat -> ew (c2_E bytes) (32 + j) = nth j (c2_ex bytes) (w64 0).
Proof.
intros bytes j Hj. unfold c2_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. reflexivity.
Qed.
Lemma c2_U : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma c2_den : forall E n v x, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof.
intros E n v x H Hv Hx. rewrite denot_lit_U, U_SOff, H. unfold w64. rewrite unsigned_lit_small by exact Hv.
rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma c2_chunk8 : forall E (H : word -> bool) (m : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H m) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E H m base off e v He Hv Hr.
apply (chunk_ok_val SEGS E _ base off 8%N e v He); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
cbn [N.to_nat]. apply (val_mem_of_rdword SEGS H m). exact Hr.
Qed.
Lemma c2_chunk1 : forall E (H : word -> bool) (m : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> aview SEGS H m (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal 1 e)).
Proof.
intros E H m base off e v He Hr.
destruct (val_mem1_of_aview SEGS H m (base + off) v Hr) as [Hvm Hv].
apply (chunk_ok_val SEGS E _ base off 1%N e v He); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Hvm].
Qed.

Section f.
Variable bytes : list Z.
Hypothesis Hbl : length bytes = 6%nat.
Hypothesis Hbr : Forall (fun v => 0 <= v < 256) bytes.
Hypothesis HG2 : getr (ms_regs ms3) 2 = w64 (c_sp1 cx).
Hypothesis HG9 : getr (ms_regs ms3) 9 = w64 (c_sp1 cx).
Hypothesis HG18 : getr (ms_regs ms3) 18 = w64 SHADOW_OFF.
Hypothesis R20 : getr (ms_regs ms3) 20 = w64 r.
Hypothesis R25 : getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs).
Hypothesis HSFR : gslots_fr cx fp W3 ms3.
Hypothesis HSLR : gslots_r cx fp W3 ms3 r (Boxreg.bx_fabric bs).
Hypothesis HCUR : gcursor cx W3 ms3 pos.
Hypothesis HS68 : gslot cx W3 ms3 0x68 i.
Hypothesis Hi64 : 0 <= i < 64.
Hypothesis HNI : c_n cx < 2 ^ 26.
Hypothesis HSH : gshadow cx fp W3 ms3 GSH_it.
Hypothesis HIN : garr8 SEGS M3 (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)).
#[local] Notation E := (c2_E bytes).

Lemma c2_atoms :
  ew E 9 = w64 (c_sp1 cx) /\ ew E 2 = w64 (c_sp1 cx) /\ ew E 18 = w64 SHADOW_OFF /\ ew E 20 = w64 r /\
  ew E 25 = w64 (Boxreg.bx_fabric bs) /\
  ew E 32 = w64 (c_p cx + pos) /\ ew E 33 = w64 (c_n cx - pos) /\ ew E 34 = w64 i /\
  ew E 35 = w64 (shadow_of_addr SHADOW_OFF (r + 8)) /\ ew E 36 = w64 (shadow_of_addr SHADOW_OFF (r + 280)) /\
  ew E 37 = w64 (Boxreg.bx_n bs) /\ ew E 38 = w64 (gF cx fp).
Proof.
rewrite !(c2_ew_reg bytes 9 9%bv), !(c2_ew_reg bytes 2 2%bv), !(c2_ew_reg bytes 18 18%bv),
  !(c2_ew_reg bytes 20 20%bv), !(c2_ew_reg bytes 25 25%bv) by reflexivity.
change 32%nat with (32 + 0)%nat. change 33%nat with (32 + 1)%nat. change 34%nat with (32 + 2)%nat.
change 35%nat with (32 + 3)%nat. change 36%nat with (32 + 4)%nat. change 37%nat with (32 + 5)%nat.
change 38%nat with (32 + 6)%nat.
rewrite !c2_ew_ex by lia. cbn [c2_ex map app nth].
repeat split; assumption.
Qed.
Lemma c2_byte_atom : forall j, (j < 6)%nat -> ew E (39 + j) = w64 (nth j bytes 0).
Proof.
intros j Hj. replace (39 + j)%nat with (32 + (7 + j))%nat by lia.
rewrite c2_ew_ex by lia. unfold c2_ex. rewrite map_app, app_nth2 by (cbn; lia). cbn [length map].
replace (7 + j - 7)%nat with j by lia. exact (map_nth w64 bytes 0 j).
Qed.


Local Ltac ck8 v S A :=
  apply (c2_chunk8 _ _ _ _ _ _ v);
  [ first [ reflexivity | (rewrite (c2_den _ _ _ _ A) by (unfold GO_PREV, GO_MAC in *; lia);
                           f_equal; unfold GO_PREV, GO_MAC; lia) ]
  | unfold GO_PREV, GO_MAC in *; lia
  | exact S ].

(* The values the seat's atoms hold are words. *)
Lemma c2_vals :
  0 <= c_p cx + pos < 2 ^ 64 /\ 0 <= c_n cx - pos < 2 ^ 26 /\
  0 <= shadow_of_addr SHADOW_OFF (r + 8) < 2 ^ 45 /\ 0 <= shadow_of_addr SHADOW_OFF (r + 280) < 2 ^ 45 /\
  0 <= Boxreg.bx_n bs <= 5 /\ 1 <= Boxreg.bx_fabric bs <= 40 /\ length bs = 288%nat.
Proof.
pose proof c2_geo as (_ & _ & (Hr16 & Hr4 & Hrc & Hria) & _ & Hinp).
pose proof asan_consts as (Hac & _).
destruct HCUR as (Hpos & _ & _).
destruct HINV as ((Hlen & HB1 & HB2 & _) & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in *.
unfold shadow_of_addr, SHADOW_OFF.
assert (r / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert ((r + 8) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert ((r + 280) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= (r + 8) / 8) by (apply Z.div_pos; lia).
assert (0 <= (r + 280) / 8) by (apply Z.div_pos; lia).
split; [destruct Hinp as [(_ & ->) | (_ & _ & Hp4 & Hpc & _)]; unfold GB_EMPTY in *; lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact Hlen.
Qed.

Lemma c2_spill_ok : forall wlo whi, 0 <= wlo -> whi <= 0x98 ->
  YP09.region_ok SEGS E M3 (c2_spill (SOff 32 0) (SOff 33 0) wlo whi).
Proof.
intros wlo whi Hw1 Hw2.
pose proof c2_geo as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF5) & (Hr16 & Hr4 & Hrc & Hria) & _ & Hinp).
pose proof asan_consts as (Hac & _).
pose proof c2_vals as (Vc & Vrem & Vs8 & Vs280 & Vn & Vfab & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
pose proof HSFR as (S18 & S28 & S70 & S78 & S80).
pose proof HSLR as (S10 & S20 & S38 & S40 & S50 & S60).
pose proof HCUR as (Hpos & S88 & S90).
pose proof HS68 as S68.
unfold gslot in S18, S28, S70, S78, S80, S10, S20, S38, S40, S50, S60, S88, S90, S68.
unfold YP09.region_ok, c2_spill. cbv zeta.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
rewrite (c2_U _ _ _ A9) by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold GB_STK. lia. }
unfold c2_slot_chunks. repeat apply Forall_cons; try apply Forall_nil.
- ck8 3 S10 A9.
- ck8 (gF cx fp) S18 A38.
- ck8 (gF cx fp + GO_PREV + 12) S20 A38.
- ck8 (gF cx fp) S28 A38.
- ck8 (shadow_of_addr SHADOW_OFF (r + 8)) S38 A35.
- ck8 (r + 280) S40 A20.
- ck8 (Boxreg.bx_fabric bs) S50 A25.
- ck8 (shadow_of_addr SHADOW_OFF (r + 280)) S60 A36.
- ck8 i S68 A34.
- ck8 (gF cx fp + GO_MAC) S70 A38.
- ck8 (gF cx fp + GO_PREV) S78 A38.
- ck8 (gF cx fp) S80 A38.
- ck8 (c_p cx + pos) S88 A32.
- ck8 (c_n cx - pos) S90 A33.
Qed.


Lemma c2_frame_ok : forall cs wlo whi, 0 <= wlo -> whi <= 512 ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) cs ->
  YP09.region_ok SEGS E M3 (c2_frame cs wlo whi).
Proof.
intros cs wlo whi Hw1 Hw2 Hcs.
pose proof c2_geo as (_ & (HF1 & HF2 & HF3 & HF4 & HF5) & _).
pose proof asan_consts as (Hac & _).
pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
pose proof HJ as (HAR3 & _).
pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hfin) as (_ & _ & Hpres & _).
rewrite EF in Hpres. change (fs_frame_bytes GB_CID) with 512 in Hpres.
unfold YP09.region_ok, c2_frame. cbv zeta.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
rewrite (c2_U _ _ _ A38) by lia.
split; [lia|]. split; [lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
Qed.

Lemma c2_rn_ok : YP09.region_ok SEGS E M3 c2_rn.
Proof.
pose proof c2_geo as (_ & _ & (Hr16 & Hr4 & Hrc & Hria) & _).
pose proof c2_vals as (_ & _ & _ & _ & Vn & _ & Hlen).
pose proof asan_consts as (Hac & _).
pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
pose proof HINV as ((_ & HB1 & _) & _).
pose proof HREG as (_ & _ & Hbs).
pose proof (ReacBoxregSetName.sn_val_mem (w_H W3) (ms_mem ms3) r bs Hbs) as Hvm.
rewrite <- (ReacBoxregSetName.sn_bx_n bs Hlen HB1) in Hvm.
unfold YP09.region_ok, c2_rn. cbv zeta.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
rewrite (c2_U _ _ _ A20) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E _ r 280 4%N (SOff 37 0) (Boxreg.bx_n bs)).
- rewrite (c2_den _ _ _ 0 A37) by lia. rewrite Z.add_0_r. reflexivity.
- cbn [Z.of_N]. lia.
- cbn [Z.of_N]. lia.
- exact Hvm.
Qed.

Lemma c2_rsh_ok : YP09.region_ok SEGS E M3 c2_rsh.
Proof.
pose proof c2_geo as (_ & _ & (Hr16 & Hr4 & Hrc & Hria) & _).
pose proof c2_vals as (_ & _ & _ & Vs280 & _).
pose proof asan_consts as (Hac & _).
pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
pose proof HJ as (HAR3 & _).
destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 c2_rblk) as [(Hr8 & _ & Hsh) _].
change (req_size REG_SIZE) with 288 in Hsh.
pose proof (Hsh 35 ltac:(split; [lia | vm_compute; reflexivity])) as H35. cbn in H35.
replace (shadow_of_addr SHADOW_OFF r + 35) with (shadow_of_addr SHADOW_OFF (r + 280)) in H35
  by (rewrite shadow_of_addr_aligned_off by exact Hr8; reflexivity).
unfold YP09.region_ok, c2_rsh. cbv zeta.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
rewrite (c2_U _ _ _ A36) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (c2_chunk1 _ _ _ _ _ _ 0); [reflexivity | rewrite Z.add_0_r; exact H35].
Qed.


(* The input bytes at the cursor: byte j of the head's list is the input byte pos + j. *)
Lemma c2_inbyte_aview : forall j, pos + Z.of_nat j < c_n cx ->
  aview SEGS (w_H W3) (ms_mem ms3) (c_p cx + pos + Z.of_nat j) = Some (c2_inbyte j).
Proof.
intros j Hj. pose proof HCUR as (Hpos & _).
assert (Hlt : (Z.to_nat pos + j < length (c_pl cx))%nat) by (unfold c_n in Hj; lia).
destruct (HIN (Z.to_nat pos + j)%nat ltac:(rewrite length_map; exact Hlt)) as [Hv Hb].
replace (c_p cx + Z.of_nat (Z.to_nat pos + j)%nat) with (c_p cx + pos + Z.of_nat j) in Hv by lia.
apply (aview_of_val_mem1 SEGS) in Hv; [|exact Hb]. rewrite Hv. f_equal.
unfold c2_inbyte. replace (Z.to_nat pos + j <? length (c_pl cx))%nat with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hlt).
apply map_nth.
Qed.

Lemma c2_inb_ok : forall kk, bytes = c2h_bytes -> (kk <= 6)%nat -> pos + Z.of_nat kk <= c_n cx ->
  YP09.region_ok SEGS E M3 (c2_inb kk).
Proof.
intros kk Hby Hk Hkn.
pose proof HCUR as (Hpos & _).
pose proof c2_vals as (Vc & _).
pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
unfold YP09.region_ok, c2_inb. cbv zeta.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
rewrite (c2_U _ _ _ A32) by lia.
pose proof c2_geo as (_ & _ & _ & _ & Hinp).
pose proof asan_consts as (Hac & _).
assert (Hend : kk <> 0%nat -> c_p cx + pos + Z.of_nat kk <= alloc_ceiling)
  by (intros Hk0; destruct Hinp as [(Hn0 & _) | (_ & _ & _ & Hpc & _)]; lia).
split; [lia|]. split; [destruct (Nat.eq_dec kk 0); [subst kk; cbn; lia | specialize (Hend n); lia]|].
split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. unfold c2_bytes in Hc. apply in_map_iff in Hc as (j & <- & Hj).
apply in_seq in Hj. 
assert (Aj : ew E (39 + j) = w64 (c2_inbyte j)).
{ rewrite c2_byte_atom by lia. rewrite Hby. unfold c2h_bytes.
  rewrite (nth_indep _ 0 (c2_inbyte 0)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity. }
assert (Vj : 0 <= c2_inbyte j < 256).
{ unfold c2_inbyte. destruct (_ <? _)%nat; [|lia].
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat pos + j) (c_pl cx) (Z_to_bv 8 0))) as Hr.
  change (bv_modulus 8) with 256 in Hr. lia. }
apply (c2_chunk1 _ _ _ _ _ _ (c2_inbyte j)).
- rewrite (c2_den _ _ _ 0 Aj) by lia. rewrite Z.add_0_r. reflexivity.
- rewrite Z.add_0_l. exact (c2_inbyte_aview j ltac:(lia)).
Qed.


(* The numbers the disjointness and the facts need, in one place. *)
Lemma c2_nums :
  2 ^ 46 <= c_sp1 cx <= 2 ^ 47 /\ c_sp1 cx mod 32 = 0 /\ c_sp1 cx + 0x98 <= 2 ^ 64 /\
  alloc_ceiling + 32768 - 287 <= c_sp1 cx /\
  4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ gF cx fp mod 64 = 0 /\
  (gF cx fp + 512 <= kLowShadowBeg \/ kHighMemBeg <= gF cx fp) /\
  4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= kLowShadowBeg \/ kHighMemBeg <= r) /\
  (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r) /\
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF (r + 280) /\ shadow_of_addr SHADOW_OFF (r + 280) + 1 <= kHighMemBeg /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
pose proof c2_geo as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF5) & (Hr16 & Hr4 & Hrc & Hria) & DRF & _).
pose proof asan_consts as (Hac & _).
unfold in_app in HF3, Hria. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *.
assert ((r + 280) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= (r + 280) / 8) by (apply Z.div_pos; lia).
repeat split; lia.
Qed.

Lemma c2h_disj : forall kk, bytes = c2h_bytes -> (kk <= 6)%nat -> pos + Z.of_nat kk <= c_n cx ->
  YP09.pairwise_disjoint E (c2h_regions kk).
Proof.
intros kk Hby Hk Hkn.
pose proof HCUR as (Hpos & _).
pose proof c2_nums as N.
pose proof c2_geo as (_ & _ & _ & _ & Hinp).
pose proof c2_vals as (Vc & Vrem & Vs8 & Vs280 & Vn & Vfab & Hlen).
pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
apply pairwise_disjoint_of_extents.
unfold c2h_regions, c2_spill, c2_frame, c2_rn, c2_rsh, c2_inb.
destruct (Nat.eqb_spec kk 0) as [Hk0 | Hk0]; cbn [app map]; unfold extent_of_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
all: rewrite (c2_U _ _ _ A9), (c2_U _ _ _ A38), (c2_U _ _ _ A20), (c2_U _ _ _ A36) by lia.
all: set (sh := shadow_of_addr SHADOW_OFF (r + 280)) in *.
- cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in N. repeat split; lia.
- rewrite (c2_U _ _ _ A32) by lia.
  destruct Hinp as [(Hn0 & _) | (Hn & _ & Hp4 & Hpc & Hpia & DPF & DPR)]; [lia|].
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app in Hpia. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in N, Hpia. repeat split; lia.
Qed.

Lemma c2h_facts : forall kk, (kk <= 6)%nat -> Z.of_nat kk = Z.min 6 (c_n cx - pos) -> facts_ok E (c2h_G kk).
Proof.
intros kk Hk Hkm.
pose proof HCUR as (Hpos & _).
pose proof c2_nums as N.
pose proof c2_geo as (_ & _ & _ & _ & Hinp).
pose proof c2_vals as (Vc & Vrem & Vs8 & Vs280 & Vn & Vfab & Hlen).
pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
split; [|split; exact I].
cbn [c2h_G f_atoms atoms_ok]. unfold afact_ok, c2_rem_fact. cbn [af_lo af_hi af_al2].
rewrite (c2_U _ _ _ A9), (c2_U _ _ _ A18), (c2_U _ _ _ A32), (c2_U _ _ _ A38), (c2_U _ _ _ A33), (c2_U _ _ _ A37)
  by (unfold SHADOW_OFF; lia).
change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
destruct N as (N1 & N2 & _ & _ & N5 & N6 & N7 & _).
pose proof asan_consts as (Hac & _).
assert (Hcur : 4096 <= c_p cx + pos <= 140737479966720)
  by (destruct Hinp as [(Hn0 & ->) | (_ & _ & Hp4 & Hpc & _)]; unfold GB_EMPTY; lia).
assert (Hrem : Z.of_nat kk <= c_n cx - pos <= (if (kk <? 6)%nat then Z.of_nat kk else 2 ^ 26)).
{ destruct (Nat.ltb_spec kk 6); lia. }
unfold C2_SB, SHADOW_OFF.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia | exact Hrem].
Qed.

Lemma c2h_sh : forall kk, (kk <= 6)%nat -> pos + Z.of_nat kk <= c_n cx ->
  sh_ok SEGS c2_Bx (c2h_SH kk) E M3.
Proof.
intros kk Hk Hkn.
pose proof HCUR as (Hpos & _).
pose proof c2_nums as N.
pose proof c2_geo as (_ & (_ & _ & HF3 & _) & _ & _ & Hinp).
pose proof c2_vals as (Vc & Vrem & Vs8 & Vs280 & Vn & Vfab & Hlen).
pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
pose proof HJ as (HAR3 & _).
assert (UB : U E c2_Bx = SHADOW_OFF) by (unfold c2_Bx; apply (U_atom E 18 _ A18); unfold SHADOW_OFF; lia).
unfold sh_ok, c2h_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UB, (U_atom E 38 _ A38) by lia. rewrite <- (aview_rd_of SEGS). split.
  + pose proof (gb_mac_ra B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR 0 6 HSH ltac:(lia) ltac:(lia)) as Hra.
    replace (gF cx fp + GO_MAC + 0) with (gF cx fp + 32) in Hra by (unfold GO_MAC; lia).
    replace (38 - 32) with 6 by lia. exact Hra.
  + intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    destruct N as (_ & _ & _ & _ & _ & _ & _ & NF & _). unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
- unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UB, (U_atom E 32 _ A32) by lia. rewrite <- (aview_rd_of SEGS).
  destruct (Nat.eq_dec kk 0) as [Hk0 | Hk0].
  + subst kk. cbn [Z.of_nat]. split; [intros x Hx; lia | intros a Ha; lia].
  + destruct Hinp as [(Hn0 & _) | (Hn & Hin3 & Hp4 & Hpc & Hpia & _)]; [lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
    split.
    * apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin3); lia.
    * intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
      unfold in_app in Hpia. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.


(* ---- the seat of the head (0x80354) ---- *)
Lemma c2h_seat : forall kk, bytes = c2h_bytes -> (kk <= 6)%nat -> Z.of_nat kk = Z.min 6 (c_n cx - pos) ->
  ms_pc_val ms3 = w64 (BASE + GP_T 2) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  st_ok_pi SEGS VAL E (c2h_ss kk) (restrict (w_H W3) ms3) /\ sh_ok SEGS c2_Bx (c2h_SH kk) E M3.
Proof.
intros kk Hby Hk Hkm Hpc Hresv Hsvc Hrom Hfr Hfcsr.
pose proof HCUR as (Hpos & _).
assert (Hkn : pos + Z.of_nat kk <= c_n cx) by lia.
split; [|exact (c2h_sh kk Hk Hkn)].
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_T 2)) M3 (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfr Hfcsr.
  destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *. subst. reflexivity. }
rewrite Hms. unfold c2h_ss. apply pa_entry_st_ok_full.
- unfold c2_E. apply regs_ok_Eimg_Ereg.
- clear - Hk. destruct kk as [|[|[|[|[|[|[|kk]]]]]]]; try lia; vm_compute; reflexivity.
- unfold c2h_regions. apply Forall_app. split.
  + apply Forall_cons; [exact (c2_spill_ok 0x88 0x98 ltac:(lia) ltac:(lia))|].
    apply Forall_cons; [exact (c2_frame_ok [] 32 38 ltac:(lia) ltac:(lia) (Forall_nil _))|].
    apply Forall_cons; [exact c2_rn_ok|].
    apply Forall_cons; [exact c2_rsh_ok | apply Forall_nil].
  + destruct (Nat.eqb_spec kk 0); [apply Forall_nil|].
    apply Forall_cons; [exact (c2_inb_ok kk Hby Hk Hkn) | apply Forall_nil].
- exact (c2h_disj kk Hby Hk Hkn).
- exact (c2h_facts kk Hk Hkm).
Qed.


(* ---- the seat of the tail (0x80614): the MAC's bytes in the frame ---- *)
Lemma c2_mac_ok : forall M : list byte, bytes = map (fun b : byte => bv_unsigned b) M -> length M = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem ms3) (gF cx fp + GO_MAC + j) =
     Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) (c2_bytes 32 6).
Proof.
intros M Hby HML HMb.
apply Forall_forall. intros c Hc. unfold c2_bytes in Hc. apply in_map_iff in Hc as (j & <- & Hj).
apply in_seq in Hj.
assert (Aj : ew E (39 + j) = w64 (bv_unsigned (nth j M (Z_to_bv 8 0)))).
{ rewrite c2_byte_atom by lia. rewrite Hby.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity. }
pose proof (bv_unsigned_in_range 8 (nth j M (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
apply (c2_chunk1 _ _ _ _ _ _ (bv_unsigned (nth j M (Z_to_bv 8 0)))).
- rewrite (c2_den _ _ _ 0 Aj) by lia. rewrite Z.add_0_r. reflexivity.
- pose proof (HMb (Z.of_nat j) ltac:(lia)) as H. rewrite Nat2Z.id in H. unfold GO_MAC in H.
  replace (gF cx fp + (32 + Z.of_nat j)) with (gF cx fp + 32 + Z.of_nat j) by lia. exact H.
Qed.

Lemma c2t_disj : YP09.pairwise_disjoint E c2t_regions.
Proof.
pose proof c2_nums as N.
pose proof c2_vals as (Vc & Vrem & Vs8 & Vs280 & Vn & Vfab & Hlen).
pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
apply pairwise_disjoint_of_extents.
unfold c2t_regions, c2_spill, c2_frame, c2_rn, c2_rsh. cbn [map]. unfold extent_of_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
rewrite (c2_U _ _ _ A9), (c2_U _ _ _ A38), (c2_U _ _ _ A20), (c2_U _ _ _ A36) by lia.
set (sh := shadow_of_addr SHADOW_OFF (r + 280)) in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in N. repeat split; lia.
Qed.

Lemma c2t_seat : forall M : list byte, bytes = map (fun b : byte => bv_unsigned b) M -> length M = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem ms3) (gF cx fp + GO_MAC + j) =
     Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) ->
  ms_pc_val ms3 = w64 (BASE + GP_F) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  st_ok_pi SEGS VAL E c2t_ss (restrict (w_H W3) ms3).
Proof.
intros M Hby HML HMb Hpc Hresv Hsvc Hrom Hfr Hfcsr.
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_F)) M3 (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfr Hfcsr.
  destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *. subst. reflexivity. }
rewrite Hms. unfold c2t_ss. apply pa_entry_st_ok_full.
- unfold c2_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold c2t_regions.
  apply Forall_cons; [exact (c2_spill_ok 0 0 ltac:(lia) ltac:(lia))|].
  apply Forall_cons; [exact (c2_frame_ok _ 0 0 ltac:(lia) ltac:(lia) (c2_mac_ok M Hby HML HMb))|].
  apply Forall_cons; [exact c2_rn_ok|].
  apply Forall_cons; [exact c2_rsh_ok | apply Forall_nil].
- exact c2t_disj.
- pose proof c2_nums as (N1 & N2 & _).
  pose proof c2_vals as (_ & _ & _ & _ & Vn & _).
  pose proof c2_atoms as (A9 & A2 & A18 & A20 & A25 & A32 & A33 & A34 & A35 & A36 & A37 & A38).
  split; [|split; exact I].
  cbn [c2t_G f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (c2_U _ _ _ A9), (c2_U _ _ _ A18), (c2_U _ _ _ A37) by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold C2_SB, SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

End f.
End e.

(* ---- the cut K and the tail's starting point ---- *)
Section g.
Variable POST : bcx -> world SEGS -> config -> Prop.
Hypothesis MTL : ameter_laws MT.
Hypothesis HK : gb_from B MT POST (GI_K B MT i).
Hypothesis HMO : mo_le MT (c_S cx) S3 acc.
Hypothesis Hk : k <= 1 + 2 * i.
Hypothesis Hacc : acc <= GB_A MT i.
Hypothesis Hi64 : 0 <= i < 64.

(* At 0x80ab4 the table is unchanged (bs' = bs) and no row was renamed (ren = -1, s5 = 0xffffffff). *)
Lemma c2_atK : forall regsK memK mdK,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 memK mdK k ->
  gb_body cx fp GP_K W3 (mkst regsK (w64 (BASE + GP_K)) memK (seg_rom SEGS)) GSH_it ->
  greg B ly3 S3 W3 (mkst regsK (w64 (BASE + GP_K)) memK (seg_rom SEGS)) r bs ->
  gprev cx fp W3 (mkst regsK (w64 (BASE + GP_K)) memK (seg_rom SEGS)) bs ->
  gslots_r cx fp W3 (mkst regsK (w64 (BASE + GP_K)) memK (seg_rom SEGS)) r (Boxreg.bx_fabric bs) ->
  gcursor cx W3 (mkst regsK (w64 (BASE + GP_K)) memK (seg_rom SEGS)) pos ->
  gslot cx W3 (mkst regsK (w64 (BASE + GP_K)) memK (seg_rom SEGS)) 0x68 i ->
  getr regsK 20 = w64 r -> getr regsK 21 = w64 4294967295 -> getr regsK 25 = w64 (Boxreg.bx_fabric bs) ->
  SRr SEGS W3 (mkCfg (mkst regsK (w64 (BASE + GP_K)) memK (seg_rom SEGS)) mdK) (POST cx).
Proof.
intros regsK memK mdK HJK HBD HRG HPV HSR HCU H68 K20 K21 K25.
apply (HK cx fp k acc ly3 S3 W3 (mkst regsK (w64 (BASE + GP_K)) memK (seg_rom SEGS)) mdK HB HJK HFR HMO).
pose proof HINV as ((_ & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
assert (HA : GB_A MT i <= GB_A MT (i + 1)).
{ unfold GB_A. pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). nia. }
exists r, bs, bs, (-1), pos.
split; [exact HBD|]. split; [exact Hi64|]. split; [lia|]. split; [lia|].
split; [exact HBLK|]. split; [exact HRG|]. split; [exact HPV|]. split; [exact HINV|]. split; [exact HINV|].
split; [reflexivity|]. split; [exact (LLVMFuzzerTestOneInput_case2.c2_kept bs)|]. split; [lia|].
split; [exact K20|]. split; [cbn [ms_regs mkst]; rewrite K21; reflexivity|]. split; [exact K25|].
split; [exact HSR|]. split; [exact HCU | exact H68].
Qed.


(* The machine state at 0x80614 (the tail's start), in the cut's vocabulary: the head has read the MAC M into
   mac[0 .. 5], the cursor is at pos, s4 = r, s5 = &mac, s9 = the fabric. *)
Definition c2_FI (ms : machine_state) (md : Model) (M : list byte) : Prop :=
  gb_body cx fp GP_F W3 ms GSH_it /\
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms) md k /\
  greg B ly3 S3 W3 ms r bs /\ gprev cx fp W3 ms bs /\ gslots_r cx fp W3 ms r (Boxreg.bx_fabric bs) /\
  gcursor cx W3 ms pos /\ gslot cx W3 ms 0x68 i /\
  getr (ms_regs ms) 20 = w64 r /\ getr (ms_regs ms) 21 = w64 (gF cx fp + GO_MAC) /\
  getr (ms_regs ms) 25 = w64 (Boxreg.bx_fabric bs) /\
  length M = 6%nat /\
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem ms) (gF cx fp + GO_MAC + j) =
     Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))).

(* The landing at K: the registers from the engine's state, the memory facts from c2_FI's by the keep zone. *)
Lemma c2_land : forall ms md M ms' md' E ss,
  c2_FI ms md M -> gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) (ms_mem ms') ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms') md' k ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms') -> ss_resv ss = None -> ss_pc ss = GP_K ->
  getr (ms_regs ms') 2 = w64 (c_sp1 cx) -> getr (ms_regs ms') 8 = w64 (spZ (c_regs cx)) ->
  getr (ms_regs ms') 9 = w64 (c_sp1 cx) -> getr (ms_regs ms') 3 = getr (c_regs cx) 3 ->
  getr (ms_regs ms') 4 = getr (c_regs cx) 4 -> getr (ms_regs ms') 18 = w64 SHADOW_OFF ->
  getr (ms_regs ms') 24 = w64 (gSH cx fp) -> getr (ms_regs ms') 20 = w64 r ->
  getr (ms_regs ms') 21 = w64 4294967295 -> getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) ->
  SRr SEGS W3 (mkCfg ms' md') (POST cx).
Proof.
intros ms md M ms' md' E ss HFI HKP HJ' HS Hrv Hpc K2 K8 K9 K3 K4 K18 K24 K20 K21 K25.
destruct HFI as (HBODY & HJ & HREG & HPREV & HSLR & HCUR & HS68 & _).
pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & HSV & HSH & Hlen & HFL & HSFR & HIN).
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS Hrv), Hpc in *.
set (msK := mkst (ms_regs ms') (Z_to_bv 64 (BASE + GP_K)) (ms_mem ms') (seg_rom SEGS)) in *.
assert (HK' : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) (ms_mem msK)) by exact HKP.
apply c2_atK.
- exact HJ'.
- unfold gb_body. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [unfold gregs; repeat split; assumption|].
  split; [eapply gb_gsaved_keep; first [exact HB | exact HK' | exact HSV]|].
  split; [eapply gb_gshadow_keep; first [exact HB | exact HK' | exact HSH | (vm_compute; discriminate)]|].
  split; [exact Hlen|].
  split; [eapply gb_flag_keep; first [exact HB | exact HK' | exact HFL]|].
  split; [eapply gb_gslots_fr_keep; first [exact HB | exact HK' | exact HSFR]|].
  eapply gb_input_keep; first [exact HB | exact HK' | exact HIN].
- eapply gb_greg_keep; first [exact HB | exact HK' | exact HREG | (left; reflexivity)].
- eapply gb_gprev_keep; first [exact HB | exact HK' | exact HPREV].
- eapply gb_gslots_r_keep; first [exact HB | exact HK' | exact HSLR].
- eapply gb_gcursor_keep; first [exact HB | exact HK' | exact HCUR].
- eapply gb_gslot_keep; first [exact HB | exact HK' | exact HS68 | lia].
- exact K20.
- exact K21.
- exact K25.
Qed.

Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HZB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HZ1 : IMG_LO + 64 <= VAL (A_OBJ 6).
Hypothesis HZ2 : VAL (A_OBJ 6) + 6 + 64 <= IMG_HI.
Hypothesis HMB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HM1 : IMG_LO + 64 <= VAL (A_OBJ 4).
Hypothesis HM2 : VAL (A_OBJ 4) + 5 + 64 <= IMG_HI.

(* A registered read-only global's bytes, read through any memory the journal reaches from the entry's. *)
Lemma c2_rom : forall a l mem md own ly' S' k',
  SnprintfDef.asn_rom_bytes SEGS B a l ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    own ly' S' W3 mem md k' ->
  forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W3) mem (a + j) = Some (nth (Z.to_nat j) l 0).
Proof.
intros a l mem md own ly' S' k' HRB HJ' j Hj.
destruct (HRB j Hj) as (Hrom & Hown & Herr & Hb).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 (a + j)).
- rewrite (HRO (a + j) ltac:(left; exact Hrom) Hown Herr). exact Hb.
- destruct Hrom as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
- exact Hown.
- exact Herr.
- apply fp_spares_closed. exact sink_closed_nil.
Qed.

Hypothesis TFIND : treac_boxreg_find_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).



(* The two bcmp calls of the tail, at their trampoline: (r + 56 z, mac, 6) and (mac, ZERO, 6). *)
Lemma c2_o16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0.
Proof.
pose proof (gb_sp_facts B MT cx HB) as (Hs1 & _). pose proof (gb_sp1_al B MT cx HB) as H.
apply Z.mod_divide in Hs1; [|lia]. apply Z.mod_divide; [lia|].
destruct Hs1 as [q1 Hq1]. apply Z.mod_divide in H; [|lia]. destruct H as [q2 Hq2]. exists (2 * q2 - q1). lia.
Qed.

Lemma c2_mac_win : forall msT mdT,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem msT) mdT k ->
  gshadow cx fp W3 msT GSH_it ->
  range_addressable (aview SEGS (w_H W3) (ms_mem msT)) SHADOW_OFF (gF cx fp + GO_MAC) 6 /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem msT)) (gF cx fp + GO_MAC) 6 /\
  amem_range (gF cx fp + GO_MAC) 6.
Proof.
intros msT mdT HJT HSHT.
pose proof (gb_F_facts B MT LAWS cx fp W3 msT ly3 S3 mdT k HB HJT HFR) as (HF1 & HF2 & HF3 & _).
pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 msT ly3 S3 mdT k HB HJT) as EF.
pose proof HJT as (HART & _).
pose proof asan_consts as (Hac & _).
split; [|split].
- pose proof (gb_mac_ra B MT LAWS cx fp W3 msT ly3 S3 mdT k HB HJT HFR 0 6 HSHT ltac:(lia) ltac:(lia)) as H.
  rewrite Z.add_0_r in H. exact H.
- apply (shadow_hull_vis_of_frame _ _ LAWS _ _ _ _ _ GB_CID fp _ _ HART ltac:(rewrite HFR; left; reflexivity));
    try rewrite EF; change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia.
- unfold amem_range, in_app in *. unfold GO_MAC, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *. lia.
Qed.

Lemma c2_bcmp0 : forall msT mdT (M : list byte) raw,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem msT) mdT k ->
  getr (ms_regs msT) 10 = w64 (gF cx fp + GO_MAC) -> getr (ms_regs msT) 11 = w64 (VAL (A_OBJ 6)) ->
  getr (ms_regs msT) 12 = w64 6 -> spZ (ms_regs msT) = c_sp1 cx ->
  getr (ms_regs msT) 3 = w64 (as_gp B) -> getr (ms_regs msT) 4 = w64 (as_tp B) ->
  getr (ms_regs msT) 1 = raw -> YK0s.ret_ok raw ->
  gshadow cx fp W3 msT GSH_it -> length M = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem msT) (gF cx fp + GO_MAC + j) =
     Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs msT) (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_bcmp)) (ms_mem msT) (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2 (v : word),
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
         [(GB_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved (ms_regs msT) regs2 /\ getr regs2 10 = v /\ (M <> Boxreg.zero6 -> v <> w64 0) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx) ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem msT) a)).
Proof.
intros msT mdT M raw HJT H10 H11 H12 Hsp H3 H4 H1 Hraw HSHT HML HMb.
pose proof HZ1 as HZ1'. pose proof HZ2 as HZ2'. unfold IMG_HI in HZ2'.
pose proof (gb_sp_facts B MT cx HB) as (Hs1 & Hs2 & Hs3 & Hs4).
pose proof (gb_sp1_al B MT cx HB) as Hs5.
pose proof (gb_F_facts B MT LAWS cx fp W3 msT ly3 S3 mdT k HB HJT HFR) as (HF1 & HF2 & HF3 & _).
pose proof (c2_mac_win msT mdT HJT HSHT) as (HMra & HMhv & HMam).
pose proof HJT as (HART & _).
pose proof asan_consts as (Hac & _).
pose proof pa_segs_low as Hsl.
assert (HZv : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem msT) (VAL (A_OBJ 6) + j) = Some 0).
{ intros j Hj. rewrite (c2_rom _ _ _ _ _ _ _ _ HZB HJT j ltac:(cbn; lia)).
  assert (Hj' : (Z.to_nat j < 6)%nat) by lia.
  unfold Boxreg.zero6. cbn [repeat map]. destruct (Z.to_nat j) as [|[|[|[|[|[|q]]]]]]; try reflexivity. lia. }
destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem msT) mdT (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
  HGLOB ltac:(unfold BX_G; left; reflexivity) HISV HART ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  as [HZra HZhv].
assert (ESTACK = 4096) as Hes by reflexivity.
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ ABCMP W3 (ms_regs msT) (ms_mem msT) GB_STK (spZ (c_regs cx)) []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 mdT k (gF cx fp + GO_MAC) (VAL (A_OBJ 6)) 6
    (c_sp1 cx - spZ (c_regs cx)) raw HJT H10 H11 H12).
  all: first [ exact H3 | exact H4 | exact H1 | exact Hraw | exact HMam | exact HMra | exact c2_o16
    | (intros _; exact HMhv)
    | exact HZra | (intros _; exact HZhv)
    | (intros a Ha; split; [|unfold GO_MAC in *; lia];
       replace a with (gF cx fp + GO_MAC + (a - (gF cx fp + GO_MAC))) by lia;
       rewrite (HMb (a - (gF cx fp + GO_MAC)) ltac:(lia)); discriminate)
    | (intros a Ha; split; [|lia];
       replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia;
       rewrite (HZv (a - VAL (A_OBJ 6)) ltac:(lia)); discriminate)
    | (unfold amem_range, kLowMemEnd; lia) | (rewrite Hsp; lia)
    | (intros a Ha; unfold GO_MAC in *; lia) | (unfold GO_MAC, GB_STK in *; lia) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hiff & Hout & _).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|].
split.
- intros HNZ Hv0. destruct (c2_nz_byte M HML HNZ) as (j & Hj & Hb).
  pose proof (proj1 Hiff Hv0 (Z.of_nat j) ltac:(lia)) as E.
  rewrite (HMb (Z.of_nat j) ltac:(lia)), (HZv (Z.of_nat j) ltac:(lia)), Nat2Z.id in E. injection E as E. exact (Hb E).
- intros a Ha Hw. apply Hout; [exact Ha|]. lia.
Qed.

Lemma c2_bcmp1 : forall msT mdT (M : list byte) raw z,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem msT) mdT k ->
  0 <= z < Boxreg.bx_n bs -> Boxreg.bx_mac bs z = M ->
  getr (ms_regs msT) 10 = w64 (r + 56 * z) -> getr (ms_regs msT) 11 = w64 (gF cx fp + GO_MAC) ->
  getr (ms_regs msT) 12 = w64 6 -> spZ (ms_regs msT) = c_sp1 cx ->
  getr (ms_regs msT) 3 = w64 (as_gp B) -> getr (ms_regs msT) 4 = w64 (as_tp B) ->
  getr (ms_regs msT) 1 = raw -> YK0s.ret_ok raw ->
  gshadow cx fp W3 msT GSH_it -> length M = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem msT) (gF cx fp + GO_MAC + j) =
     Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) ->
  (forall j, 0 <= j < REG_SIZE -> aview SEGS (w_H W3) (ms_mem msT) (r + j) =
     Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs msT) (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_bcmp)) (ms_mem msT) (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
         [(GB_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved (ms_regs msT) regs2 /\ getr regs2 10 = w64 0 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx) ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem msT) a)).
Proof.
intros msT mdT M raw z HJT Hz HMz H10 H11 H12 Hsp H3 H4 H1 Hraw HSHT HML HMb HRb.
pose proof (gb_sp_facts B MT cx HB) as (Hs1 & Hs2 & Hs3 & Hs4).
pose proof (gb_F_facts B MT LAWS cx fp W3 msT ly3 S3 mdT k HB HJT HFR) as (HF1 & HF2 & HF3 & _).
pose proof (c2_mac_win msT mdT HJT HSHT) as (HMra & HMhv & HMam).
pose proof HJT as (HART & _).
pose proof asan_consts as (Hac & _).
pose proof HINV as ((Hlen & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HART c2_rblk) as (Hr16 & Hr4096 & Hrc & Hria & _).
change (req_size REG_SIZE) with 288 in Hrc, Hria.
assert (ESTACK = 4096) as Hes by reflexivity.
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ ABCMP W3 (ms_regs msT) (ms_mem msT) GB_STK (spZ (c_regs cx)) []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 mdT k (r + 56 * z) (gF cx fp + GO_MAC) 6
    (c_sp1 cx - spZ (c_regs cx)) raw HJT H10 H11 H12).
  all: first [ exact H3 | exact H4 | exact H1 | exact Hraw | exact HMam | exact HMra | exact c2_o16
    | (intros _; exact HMhv)
    | (intros a Ha; split; [|lia];
       replace a with (r + (a - r)) by lia; rewrite (HRb (a - r) ltac:(unfold REG_SIZE; lia)); discriminate)
    | (intros a Ha; split; [|unfold GO_MAC in *; lia];
       replace a with (gF cx fp + GO_MAC + (a - (gF cx fp + GO_MAC))) by lia;
       rewrite (HMb (a - (gF cx fp + GO_MAC)) ltac:(lia)); discriminate)
    | (apply (amem_range_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ HART c2_rblk); change (req_size REG_SIZE) with 288; lia)
    | (apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ HART c2_rblk); change (req_size REG_SIZE) with 288; lia)
    | (intros _; apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ HART c2_rblk); change (req_size REG_SIZE) with 288; lia)
    | (unfold amem_range, kLowMemEnd; lia) | (rewrite Hsp; lia)
    | (intros a Ha; unfold GO_MAC in *; lia) | (unfold GO_MAC, GB_STK in *; lia) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hiff & Hout & _).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split.
- rewrite Hv. apply (proj2 Hiff). intros j Hj.
  rewrite (HMb j Hj). replace (r + 56 * z + j) with (r + (56 * z + j)) by lia.
  rewrite (HRb (56 * z + j) ltac:(unfold REG_SIZE; lia)). do 2 f_equal.
  rewrite <- HMz. rewrite (c2_mac_nth bs z (Z.to_nat j) ltac:(lia) ltac:(lia)). f_equal. lia.
- intros a Ha Hw. apply Hout; [exact Ha|]. lia.
Qed.

Lemma c2_gsaved_s0 : forall ms, gsaved cx W3 ms ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
intros ms [_ H]. specialize (H 0 ltac:(lia)). rewrite Z.mul_0_r, Z.sub_0_r in H. rewrite H.
unfold s0Z. do 3 f_equal; apply bv_eq; reflexivity.
Qed.
Lemma c2_achain : forall ly3' S3' W3' mem md own k' sp',
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    own ly3' S3' W3' mem md k' ->
  rdword (aview SEGS (w_H W3') mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3') mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain ly3' (aview SEGS (w_H W3') mem) sp' (spZ (c_regs cx)) (gch cx).
Proof.
intros ly3' S3' W3' mem md own k' sp' HJ' H8 H16 Hsp.
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof HJ' as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
apply (achain_ly_top (c_ly cx) ly3' _ _ _ _ Etop).
eapply (gb_achain B MT cx HB);
  first [ exact H8 | exact H16 | exact Hsp | (intros a Ha; apply F1; unfold GB_STK in *; lia) ].
Qed.
(* A signed branch between two words that hold small values, as a fact on Z. *)
Lemma c2_lts : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. apply Boxreg.lts_lit; lia. Qed.
Lemma c2_m1 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma c2_sh280 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> In (r, REG_SIZE) (ablocks B ly S) ->
  aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF (r + 280)) = Some 0.
Proof.
intros ly S W mem md HAR Hin.
destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as [(Hr8 & _ & Hsh) _].
change (req_size REG_SIZE) with 288 in Hsh.
pose proof (Hsh 35 ltac:(split; [lia | vm_compute; reflexivity])) as H35. cbn in H35.
rewrite shadow_of_addr_aligned_off by exact Hr8. exact H35.
Qed.
Lemma c2_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma c2_den_row : forall E z, ew E 20 = Z_to_bv 64 r -> ew E 49 = Z_to_bv 64 z ->
  0 <= r -> 0 <= z <= 4 -> r + 56 * z < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 20 0) (SMd M_MUL (SOff 49 0) (SLit 56))) = Z_to_bv 64 (r + 56 * z).
Proof.
intros E z H20 H49 Hr Hz Hlt. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E 49 z H49) by lia. rewrite U_SOff, H20, U_SLit.
rewrite unsigned_lit_small by lia.
rewrite (zcanon_id 56) by (unfold M64; lia). rewrite (zcanon_id (r + 0)) by (unfold M64; lia).
rewrite (zcanon_id (z * 56)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* A call whose post keeps every byte outside [sp1 - 2 ESTACK, sp1) keeps the phase's zone. *)
Lemma c2_keep_win : forall m m' (ms : machine_state) md,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx) ->
     aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  gb_keep cx fp W3 [(r, REG_SIZE)] m m'.
Proof.
intros m m' ms md HJT Hout a Ha.
pose proof (c2_geo ms md HJT)
  as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF5) & (Hr16 & Hr4 & Hrc & Hria) & _ & Hinp).
pose proof asan_consts as (Hac & _).
assert (ESTACK = 4096) as Hes by reflexivity.
apply Hout.
- destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  + lia.
  + destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc & _)]; [unfold c_n in *; lia | lia].
  + change (fs_frame_bytes GB_CID) with 512 in Ha. lia.
  + change (fs_frame_bytes GB_CID / 8) with 64 in Ha. rewrite HF5 in Ha.
    assert (gF cx fp / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= gF cx fp / 8) by (apply Z.div_pos; lia). unfold in_zr, SHADOW_OFF in *; cbn [fst snd] in *. lia.
  + apply Exists_cons in Ha as [Ha | Ha]; [cbn [fst snd] in Ha; unfold REG_SIZE in Ha; lia | inversion Ha].
- destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  + lia.
  + destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc & _)]; [unfold c_n in *; lia | lia].
  + change (fs_frame_bytes GB_CID) with 512 in Ha. lia.
  + change (fs_frame_bytes GB_CID / 8) with 64 in Ha. rewrite HF5 in Ha.
    assert (gF cx fp / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= gF cx fp / 8) by (apply Z.div_pos; lia). unfold in_zr, SHADOW_OFF in *; cbn [fst snd] in *. lia.
  + apply Exists_cons in Ha as [Ha | Ha]; [cbn [fst snd] in Ha; unfold REG_SIZE in Ha; lia | inversion Ha].
Qed.

(* A register's value at a call stop, as the engine's term (no normalization). *)
Local Ltac prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* A run that writes nothing (no region has a window): the zone is kept. *)
Local Ltac c2_nw HKA :=
  lazymatch type of HKA with gb_keep ?c ?f ?w ?rs ?m0 ?mO =>
  lazymatch goal with HFx : frame_of _ _ mO (ms_mem ?msN) |- _ =>
    let Hm := fresh "Hm" in
    assert (Hm : forall x, ms_mem msN x = mO x);
    [ intros x; apply HFx; intros (rg & Hin & Hb); vm_compute in Hin;
      repeat (destruct Hin as [<- | Hin]; [cbn in Hb; lia |]); destruct Hin
    | let HK' := fresh "HKA" in
      assert (HK' : gb_keep c f w rs m0 (ms_mem msN)) by (eapply gb_keep_trans; [exact HKA | apply gb_keep_pointwise; exact Hm]);
      clear HKA Hm; rename HK' into HKA ]
  end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* A register of the engine's state whose value is one of the seat's registers. *)
Local Ltac c2_reg Q OLDs F :=
  rewrite Q; repeat (rewrite OLDs by lia); exact F.

(* The landing at K from the engine's state at 0x80ab4: the registers the cut names. *)
Local Ltac c2_atK_tac HFI0 HKA HS ro Hgp0 Htp0 :=
  lazymatch goal with |- SRr _ _ (mkCfg ?msK ?mdK) _ =>
  let K2 := fresh "K2" in let K8 := fresh "K8" in let K9 := fresh "K9" in let K3 := fresh "K3" in
  let K4 := fresh "K4" in let K18 := fresh "K18" in let K24 := fresh "K24" in let K20 := fresh "K20" in
  let K21 := fresh "K21" in let K25 := fresh "K25" in
  prreg HS (2%bv : bv 5) K2; prreg HS (8%bv : bv 5) K8; prreg HS (9%bv : bv 5) K9;
  prreg HS (3%bv : bv 5) K3; prreg HS (4%bv : bv 5) K4; prreg HS (18%bv : bv 5) K18;
  prreg HS (24%bv : bv 5) K24; prreg HS (20%bv : bv 5) K20; prreg HS (21%bv : bv 5) K21;
  prreg HS (25%bv : bv 5) K25;
  eapply (c2_land _ _ _ msK mdK _ _ HFI0 HKA ltac:(eassumption) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
  [ rewrite K2; ro; unfold w64; assumption
  | rewrite K8; ro; unfold w64; assumption
  | rewrite K9; ro; unfold w64; assumption
  | rewrite K3; ro; rewrite Hgp0; unfold w64; assumption
  | rewrite K4; ro; rewrite Htp0; unfold w64; assumption
  | rewrite K18; ro; unfold w64; assumption
  | rewrite K24; ro; unfold w64; assumption
  | rewrite K20; ro; unfold w64; assumption
  | rewrite K21; reflexivity
  | rewrite K25; ro; unfold w64; assumption ]
  end.

Lemma c2_tail : forall ms md M, c2_FI ms md M -> SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
intros ms md M HFI. pose proof HFI as HFI0.
destruct HFI as (HBODY & HJ & HREG & HPREV & HSLR & HCUR & HS68 & R20 & R21 & R25 & HML & HMb).
pose proof HJ as HJ0.
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & HSV & HSH & Hlen & HFL & HSFR & HIN).
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE0 & HE02 & _).
set (bytes := map (fun b : byte => bv_unsigned b) M).
assert (HS : st_ok_pi SEGS VAL (c2_E ms bytes) c2t_ss (restrict (w_H W3) ms)).
{ eapply c2t_seat; try eassumption; try reflexivity.
  - subst bytes. rewrite length_map. exact HML.
  - exact (proj2 c2_cn). }
assert (Hbl : length bytes = 6%nat) by (subst bytes; rewrite length_map; exact HML).
pose proof (c2_atoms ms bytes Hbl G2 G9 G18 R20 R25 Hi64) as AT.
destruct AT as (F9 & F2 & F18 & F20 & F25 & F32 & F33 & F34 & F35 & F36 & F37 & F38).
assert (F3 : ew (c2_E ms bytes) 3 = w64 (as_gp B)) by (rewrite (c2_ew_reg ms bytes 3 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew (c2_E ms bytes) 4 = w64 (as_tp B)) by (rewrite (c2_ew_reg ms bytes 4 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew (c2_E ms bytes) 8 = w64 (spZ (c_regs cx))) by (rewrite (c2_ew_reg ms bytes 8 8%bv eq_refl); exact G8).
assert (F21 : ew (c2_E ms bytes) 21 = w64 (gF cx fp + GO_MAC)) by (rewrite (c2_ew_reg ms bytes 21 21%bv eq_refl); exact R21).
assert (F24 : ew (c2_E ms bytes) 24 = w64 (gSH cx fp)) by (rewrite (c2_ew_reg ms bytes 24 24%bv eq_refl); exact G24).
assert (HEI : img_env VAL A_LIM (c2_E ms bytes)) by (unfold c2_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS c2_Bx [] (c2_E ms bytes) (mrestrict (w_H W3) (ms_mem ms))) by constructor.
remember (c2_E ms bytes) as E eqn:HE.
unfold w64 in F2, F3, F4, F8, F9, F18, F20, F21, F24, F25, F32, F33, F34, F35, F36, F37, F38.
paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |].
(* No window is writable: the run kept the memory. *)
lazymatch goal with HFx : frame_of _ _ (ms_mem ms) (ms_mem ?msN) |- _ =>
  assert (Hmeq : forall x, ms_mem msN x = ms_mem ms x);
  [ intros x; apply HFx; intros (rg & Hin & Hb); vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn in Hb; lia |]); destruct Hin
  | ]; rename msN into ms1 end.
assert (HKA : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) (ms_mem ms1)) by (apply gb_keep_pointwise; exact Hmeq).
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite pa_sigma_reac_boxreg_find.
assert (AV1 : forall a, aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms) a)
  by (intros a; unfold aview, YP09.mbyte, mrestrict; rewrite Hmeq; reflexivity).
pose proof c2_cn as Hcn.
pose proof (c2_nums ms1 _ HJ bytes Hbl Hi64) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
pose proof (gb_sp_facts B MT cx HB) as (Hs1 & Hs2 & Hs3 & Hs4).
pose proof pa_B_ok as HBok. pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof HINV as ((Hlen288 & HB1 & _) & _).
pose proof HREG as (_ & _ & Hbs).
assert (Qsp : spZ (ms_regs ms1) = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
  by (unfold spZ at 1; rewrite Q2, F2, unsigned_lit_small by lia; lia).
assert (S8 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
  by (destruct HSV as [H8 _]; unfold rdword in *; rewrite !AV1; exact H8).
assert (S16 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)))
  by (pose proof (c2_gsaved_s0 ms HSV) as H; unfold rdword in *; rewrite !AV1; exact H).
assert (HSH1 : gshadow cx fp W3 ms1 GSH_it) by (intros j Hj; rewrite AV1; exact (HSH j Hj)).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs ms1) (ms_mem ms1) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k REAC_BOXREG_FIND_STK [] 0 (c_sp1 cx - spZ (c_regs cx))
    (getr (ms_regs ms1) 1) (gch cx)
    (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
       (forall j, 0 <= j < REG_SIZE -> aview SEGS (w_H W2) mem2 (r + j) =
          Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0)))) /\
       (forall j, 0 <= j < 6 -> aview SEGS (w_H W2) mem2 (gF cx fp + GO_MAC + j) =
          Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) /\
       exists z, getr regs2 10 = w64 z /\ reac_boxreg_find_c.find_result bs M z) HJ Qsp).
  - pose proof (gb_sp1_al B MT cx HB). apply Z.mod_divide in Hs1; [|lia]. apply Z.mod_divide; [lia|].
    destruct Hs1 as [q1 Hq1]. apply Z.mod_divide in H; [|lia]. destruct H as [q2 Hq2]. exists (2 * q2 - q1). lia.
  - lia.
  - unfold REAC_BOXREG_FIND_STK, ESTACK. lia.
  - unfold REAC_BOXREG_FIND_STK, ESTACK, GB_STK. lia.
  - rewrite Q3, F3. reflexivity.
  - rewrite Q4, F4. reflexivity.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
    unfold s0Z at 1. rewrite Q8, F8, unsigned_lit_small by lia.
    exact (c2_achain ly3 S3 W3 (ms_mem ms1) _ _ _ (c_sp1 cx) HJ S8 S16 ltac:(lia)).
  - intros HPRE1.
    assert (HAF : afobj SEGS B ly3 S3 W3 (ms_mem ms1) (gF cx fp + GO_MAC) 6).
    { pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms1 ly3 S3 _ k HB HJ) as EF.
      assert (HF8 : gF cx fp mod 8 = 0).
      { apply Z.mod_divide in N7; [|lia]. apply Z.mod_divide; [lia|]. destruct N7 as [q Hq]. exists (8 * q). lia. }
      split.
      - exists GB_CID, fp. rewrite EF. change (fs_frame_bytes GB_CID) with 512.
        split; [rewrite HFR; left; reflexivity|]. split; [unfold GB_CID; lia|].
        split; [exact HF8|]. unfold GO_MAC. lia.
      - split.
        + unfold GO_MAC. rewrite Z.add_mod, HF8 by lia. reflexivity.
        + pose proof (gb_mac_ra B MT LAWS cx fp W3 ms1 ly3 S3 _ k HB HJ HFR 0 6 HSH1 ltac:(lia) ltac:(lia)) as H.
          rewrite Z.add_0_r in H. exact H. }
    eapply SRr_mono.
    { exact (TFIND ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ (gch cx) r (gF cx fp + GO_MAC) bs M HPRE1
        ltac:(rewrite Q10, F20; reflexivity) ltac:(rewrite Q11, F21; reflexivity) c2_rblk Hlen288
        ltac:(intros j Hj; rewrite AV1; exact (Hbs j Hj)) HB1 HAF HML
        ltac:(intros j Hj; rewrite AV1; exact (HMb j Hj))). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & Hc & HJ' & HP' & (Hly & HS' & HW & _ & HR & HMm & Hz')).
    exists ly', S', regs', mem', md'. split; [exact Hc|]. split; [exact HJ'|]. split; [exact HP'|].
    subst ly' S' W'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact HR|]. split; [exact HMm | exact Hz'].
  - intros a (rgx & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & HRB & HMB2 & z & Hz & FRz)).
rewrite Z.add_0_r in HJ2.
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
assert (HKC : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms1) mem2).
{ eapply gb_keep_call; first [ exact LAWS | exact HB | exact HJ | exact HFR | lia | exact HJc
    | (intros p0 n0 Hp0; unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hp0)
    | (constructor; [|constructor]; exists REG_SIZE; cbn [fst snd];
       split; [exact c2_rblk | change (req_size REG_SIZE) with 288; unfold REG_SIZE; lia]) ]. }
pose proof HJ as (HAR1 & _). pose proof HJ2 as (HAR2 & _).
assert (HKA2 : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) mem2) by (eapply gb_keep_trans; [exact HKA | exact HKC]).
clear HKA.
jafter_call_keep_pi HS 45%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ unfold c2_spill, c2_frame, c2_rn, c2_rsh.
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val];
    try (intros a Ha; lia);
    intros a Ha; apply (mbyte_of_aview SEGS).
  - rewrite F9, unsigned_lit_small in Ha by lia. apply HKC. left. lia.
  - rewrite F38, unsigned_lit_small in Ha by lia. apply HKC. right; right; left. change (fs_frame_bytes GB_CID) with 512. lia.
  - rewrite F20, unsigned_lit_small in Ha by lia. apply HKC. right; right; right; right.
    apply Exists_cons_hd. cbn [fst snd]. unfold REG_SIZE. lia.
  - assert (Vsh : 0 <= shadow_of_addr SHADOW_OFF (r + 280) < 2 ^ 64)
      by (clear - N13 N14; set (sh := shadow_of_addr SHADOW_OFF (r + 280)) in *; unfold SHADOW_OFF, kHighMemBeg in *; lia).
    rewrite F36, unsigned_lit_small in Ha by exact Vsh.
    replace a with (shadow_of_addr SHADOW_OFF (r + 280)) by lia.
    rewrite (c2_sh280 _ _ _ _ _ HAR2 c2_rblk), (c2_sh280 _ _ _ _ _ HAR1 c2_rblk). reflexivity. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite Q1.
remember (havoc E 45 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall q, (q < 45)%nat -> ew E1 q = ew E q)
  by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
assert (Fz : ew E1 49 = Z_to_bv 64 z).
{ rewrite HE1. change 49%nat with (45 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E 45 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
  cbn [nth map]. exact Hz. }
clear HE1.
pose proof (c2_find_range bs M z HB1 FRz) as Hzr.
pose proof HB1 as HB1'. unfold Boxreg.boxreg_B1 in HB1'.
assert (SHOK1 : sh_ok SEGS c2_Bx [] E1 (mrestrict (w_H W3) mem2)) by constructor.
clear SHOK HJ HJc. rename SHOK1 into SHOK. rename HJ2 into HJ.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
psrr_branch_tok RUN BR HS SHOK c2_span.
{ (* z < -1: refuted by find's result *)
  exfalso. rewrite c2_denot0, Fz in Hc. cbn [sv_denot branch_taken] in Hc.
  rewrite c2_m1, c2_lts in Hc by lia.
  apply Z.ltb_lt in Hc. lia. }
rewrite c2_denot0, Fz in Hc. cbn [sv_denot branch_taken] in Hc. rewrite c2_m1, c2_lts in Hc by lia.
apply Z.ltb_ge in Hc. clear Hc.
paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
psrr_branch_tok RUN BR HS SHOK c2_span.
{ (* z >= r->n: refuted by find's result *)
  exfalso. rewrite !c2_denot0, Fz, (OLD1 37%nat ltac:(lia)), F37 in Hc. cbn [branch_taken] in Hc.
  rewrite c2_lts in Hc by lia. apply Bool.negb_true_iff, Z.ltb_ge in Hc. lia. }
rewrite !c2_denot0, Fz, (OLD1 37%nat ltac:(lia)), F37 in Hc. cbn [branch_taken] in Hc.
rewrite c2_lts in Hc by lia. apply Bool.negb_false_iff, Z.ltb_lt in Hc. clear Hc.
paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
psrr_branch_tok RUN BR HS SHOK c2_span.
{ (* z < 0, so z = -1 *)
  rewrite !c2_denot0, Fz in Hc. cbn [sv_denot branch_taken] in Hc.
  rewrite c2_lts in Hc by lia. apply Z.ltb_lt in Hc. assert (Ez : z = -1) by lia. subst z. clear Hc.
  paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?mT) _ _ _) ?mdT) _ => rename mT into msT end.
  assert (HSHT : gshadow cx fp W3 msT GSH_it) by (eapply gb_gshadow_keep; first [exact HKA2 | exact HSH | (vm_compute; discriminate)]).
  assert (HMbT : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem msT) (gF cx fp + GO_MAC + j) =
     Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0))))
    by (intros j Hj; rewrite (HKA2 (gF cx fp + GO_MAC + j)); [exact (HMb j Hj) | right; right; left;
        change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia]).
  eapply SRr_bind.
  { apply (c2_bcmp0 msT _ M (getr (ms_regs msT) 1) HJ).
    - rewrite T10, (OLD1 21%nat ltac:(lia)). exact F21.
    - rewrite T11. change 247%nat with (A_OBJ 6). apply (img_env_atomP E1 (A_OBJ 6) HEI1). unfold A_OBJ, A_TEXT, A_LIM. lia.
    - exact T12.
    - unfold spZ. rewrite T2, (OLD1 2%nat ltac:(lia)), F2, unsigned_lit_small by lia. reflexivity.
    - rewrite T3, (OLD1 3%nat ltac:(lia)). exact F3.
    - rewrite T4, (OLD1 4%nat ltac:(lia)). exact F4.
    - reflexivity.
    - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - exact HSHT.
    - exact HML.
    - exact HMbT. }
  cbv beta. intros W2' c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hnz & Hout).
  assert (HKA3 : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) mem3)
    by (eapply gb_keep_trans; [exact HKA2 | exact (c2_keep_win _ _ msT _ HJ Hout)]).
  clear HKA2. rename HKA3 into HKA2.
  jafter_call_keep_pi HS 61%nat regs3 (mrestrict (w_H W3) mem3) HP3 (@nil nat) HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { constructor. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  rewrite T1.
  remember (havoc E1 61 (map (getr regs3) CLOB)) as E2 eqn:HE2 in HS.
  assert (HIE2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
  assert (OLD2 : forall q, (q < 61)%nat -> ew E2 q = ew E1 q)
    by (intros q Hq; rewrite HE2; apply YN3v.ew_havoc_old; exact Hq).
  clear HE2.
  assert (SHOK2 : sh_ok SEGS c2_Bx [] E2 (mrestrict (w_H W3) mem3)) by constructor.
  clear SHOK HJ. rename SHOK2 into SHOK. rename HJ3 into HJ.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
  psrr_branch_tok RUN BR HS SHOK c2_span.
  2: { exfalso. rewrite branch_eq_U, U_SOff, (OLD2 49%nat ltac:(lia)), Fz, U_SLit in Hc. vm_compute in Hc. discriminate. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_K; [awr_ok_tac |]. c2_nw HKA2.
  c2_atK_tac HFI0 HKA2 HS ltac:(repeat first [rewrite OLD2 by lia | rewrite OLD1 by lia]) Hgp0 Htp0. }
(* z >= 0: box z holds the MAC *)
rewrite !c2_denot0, Fz in Hc. cbn [sv_denot branch_taken] in Hc. rewrite c2_lts in Hc by lia.
apply Z.ltb_ge in Hc. rename Hc into Hz0.
destruct (c2_find_hit bs M z FRz Hz0) as [HMz HNZ].
pose proof (gb_F_facts B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ0 HFR) as (HFF1 & HFF2 & _).
paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg_raw HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?mT) _ _ _) ?mdT) _ => rename mT into msT end.
assert (HSHT : gshadow cx fp W3 msT GSH_it) by (eapply gb_gshadow_keep; first [exact HKA2 | exact HSH | (vm_compute; discriminate)]).
assert (HMbT : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem msT) (gF cx fp + GO_MAC + j) =
   Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0))))
  by (intros j Hj; rewrite (HKA2 (gF cx fp + GO_MAC + j)); [exact (HMb j Hj) | right; right; left;
      change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia]).
assert (HRbT : forall j, 0 <= j < REG_SIZE -> aview SEGS (w_H W3) (ms_mem msT) (r + j) =
   Some (bv_unsigned (nth (Z.to_nat j) bs (Z_to_bv 8 0))))
  by (intros j Hj; rewrite (HKA2 (r + j)); [exact (Hbs j Hj) | right; right; right; right;
      apply Exists_cons_hd; cbn [fst snd]; unfold REG_SIZE in *; lia]).
eapply SRr_bind.
{ apply (c2_bcmp1 msT _ M (getr (ms_regs msT) 1) z HJ ltac:(lia) HMz).
  - rewrite T10. apply c2_den_row; [rewrite (OLD1 20%nat ltac:(lia)); exact F20 | exact Fz | lia | lia | lia].
  - rewrite T11, (OLD1 21%nat ltac:(lia)). exact F21.
  - exact T12.
  - unfold spZ. rewrite T2, (OLD1 2%nat ltac:(lia)), F2, unsigned_lit_small by lia. reflexivity.
  - rewrite T3, (OLD1 3%nat ltac:(lia)). exact F3.
  - rewrite T4, (OLD1 4%nat ltac:(lia)). exact F4.
  - reflexivity.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HSHT.
  - exact HML.
  - exact HMbT.
  - exact HRbT. }
cbv beta. intros W2' c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hv0 & Hout).
assert (HKA3 : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) mem3)
  by (eapply gb_keep_trans; [exact HKA2 | exact (c2_keep_win _ _ msT _ HJ Hout)]).
clear HKA2 Hout. rename HKA3 into HKA2.
jafter_call_keep_pi HS 61%nat regs3 (mrestrict (w_H W3) mem3) HP3 (@nil nat) HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ constructor. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite T1.
remember (havoc E1 61 (map (getr regs3) CLOB)) as E2 eqn:HE2 in HS.
assert (HIE2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (OLD2 : forall q, (q < 61)%nat -> ew E2 q = ew E1 q)
  by (intros q Hq; rewrite HE2; apply YN3v.ew_havoc_old; exact Hq).
assert (Fv0 : ew E2 65 = Z_to_bv 64 0).
{ rewrite HE2. change 65%nat with (61 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E1 61 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
  cbn [nth map]. exact Hv0. }
clear HE2.
assert (SHOK2 : sh_ok SEGS c2_Bx [] E2 (mrestrict (w_H W3) mem3)) by constructor.
clear SHOK HJ. rename SHOK2 into SHOK. rename HJ3 into HJ.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
psrr_branch_tok RUN BR HS SHOK c2_span.
{ (* bcmp (r->box[z].mac, mac, 6) <> 0: refuted, the bytes are equal *)
  exfalso. rewrite branch_ne_U, U_SOff, Fv0, U_SLit in Hc. vm_compute in Hc. discriminate. }
clear Hc.
paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
pmkst HS.
clear T1 T2 T3 T4 T10 T11 T12.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
clear HSHT HMbT HRbT.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?mT) _ _ _) ?mdT) _ => rename mT into msU end.
assert (HSHT : gshadow cx fp W3 msU GSH_it) by (eapply gb_gshadow_keep; first [exact HKA2 | exact HSH | (vm_compute; discriminate)]).
assert (HMbT : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem msU) (gF cx fp + GO_MAC + j) =
   Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0))))
  by (intros j Hj; rewrite (HKA2 (gF cx fp + GO_MAC + j)); [exact (HMb j Hj) | right; right; left;
      change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia]).
eapply SRr_bind.
{ apply (c2_bcmp0 msU _ M (getr (ms_regs msU) 1) HJ).
  - rewrite T10, (OLD2 21%nat ltac:(lia)), (OLD1 21%nat ltac:(lia)). exact F21.
  - rewrite T11. change 247%nat with (A_OBJ 6). apply (img_env_atomP E2 (A_OBJ 6) HIE2). unfold A_OBJ, A_TEXT, A_LIM. lia.
  - exact T12.
  - unfold spZ. rewrite T2, (OLD2 2%nat ltac:(lia)), (OLD1 2%nat ltac:(lia)), F2, unsigned_lit_small by lia. reflexivity.
  - rewrite T3, (OLD2 3%nat ltac:(lia)), (OLD1 3%nat ltac:(lia)). exact F3.
  - rewrite T4, (OLD2 4%nat ltac:(lia)), (OLD1 4%nat ltac:(lia)). exact F4.
  - reflexivity.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HSHT.
  - exact HML.
  - exact HMbT. }
cbv beta. intros W2'' c4 _ (-> & regs4 & mem4 & md4 & v & -> & HJ4 & HP4 & Hv & Hnz & Hout).
assert (HKA3 : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms) mem4)
  by (eapply gb_keep_trans; [exact HKA2 | exact (c2_keep_win _ _ msU _ HJ Hout)]).
clear HKA2 Hout. rename HKA3 into HKA2.
jafter_call_keep_pi HS 77%nat regs4 (mrestrict (w_H W3) mem4) HP4 (@nil nat) HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ constructor. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite T1.
remember (havoc E2 77 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS.
assert (HIE3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HIE2 | cbv; lia]).
assert (OLD3 : forall q, (q < 77)%nat -> ew E3 q = ew E2 q)
  by (intros q Hq; rewrite HE3; apply YN3v.ew_havoc_old; exact Hq).
assert (Fv : ew E3 81 = v).
{ rewrite HE3. change 81%nat with (77 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E2 77 (map (getr regs4) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
  cbn [nth map]. exact Hv. }
clear HE3.
assert (SHOK3 : sh_ok SEGS c2_Bx [] E3 (mrestrict (w_H W3) mem4)) by constructor.
clear SHOK HJ. rename SHOK3 into SHOK. rename HJ4 into HJ.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
psrr_branch_tok RUN BR HS SHOK c2_span.
{ (* idx = -1: refuted, idx >= 0 here *)
  exfalso. rewrite branch_eq_U, U_SOff, (OLD3 49%nat ltac:(lia)), (OLD2 49%nat ltac:(lia)), Fz, U_SLit in Hc.
  rewrite unsigned_lit_small in Hc by lia. apply Z.eqb_eq in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). lia. }
clear Hc.
paj_run_tok RUN HS HJ SHOK c2_span; [awr_ok_tac |]. c2_nw HKA2.
psrr_branch_tok RUN BR HS SHOK c2_span.
{ (* bcmp (mac, ZERO, 6) = 0 with idx <> -1: refuted, the MAC is not the zero MAC *)
  exfalso. rewrite branch_eq_U, U_SOff, Fv, U_SLit in Hc. apply Z.eqb_eq in Hc. apply (Hnz HNZ).
  pose proof (bv_unsigned_in_range 64 v) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  rewrite Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
  apply bv_eq. rewrite Hc. reflexivity. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_K; [awr_ok_tac |]. c2_nw HKA2.
c2_atK_tac HFI0 HKA2 HS ltac:(repeat first [rewrite OLD3 by lia | rewrite OLD2 by lia | rewrite OLD1 by lia]) Hgp0 Htp0.
Qed.

(* ---- the head: from the T-seat (0x80354) through read_mac to 0x80614 (FI) ---- *)
(* A keep over the phase's zone but the MAC window [F+32, F+38) and the cursor window [sp1+0x88, sp1+0x98). *)
Definition c2_hkeep (m m' : word -> option byte) : Prop :=
  forall a, gb_keep_at cx fp [(r, REG_SIZE)] a -> ~ (gF cx fp + GO_MAC <= a < gF cx fp + GO_MAC + 6) ->
    ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Lemma c2_hk_refl : forall m, c2_hkeep m m.
Proof. intros m a _ _ _. reflexivity. Qed.
Lemma c2_hk_trans : forall m1 m2 m3, c2_hkeep m1 m2 -> c2_hkeep m1 m2 -> c2_hkeep m2 m3 -> c2_hkeep m1 m3.
Proof. intros m1 m2 m3 _ H1 H2 a Ha H3 H4. rewrite (H2 a Ha H3 H4). exact (H1 a Ha H3 H4). Qed.
Lemma c2_hk_pw : forall m m', (forall x, m' x = m x) -> c2_hkeep m m'.
Proof. intros m m' Hm a _ _ _. unfold aview, YP09.mbyte, mrestrict. rewrite Hm. reflexivity. Qed.
(* reading an 8-byte word / 1 byte through c2_hkeep at an address that is in the zone and off the two windows *)
Lemma c2_hk_rd : forall m m' a v, c2_hkeep m m' ->
  (forall o, 0 <= o < 8 -> gb_keep_at cx fp [(r, REG_SIZE)] (a + o) /\
     ~ (gF cx fp + GO_MAC <= a + o < gF cx fp + GO_MAC + 6) /\ ~ (c_sp1 cx + 0x88 <= a + o < c_sp1 cx + 0x98)) ->
  rdword (aview SEGS (w_H W3) m) a = Some v -> rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
intros m m' a v HKp Hdom Hr. rewrite <- Hr. apply rdword_ext. intros o Ho.
destruct (Hdom o Ho) as (G1 & G2 & G3). apply (HKp (a + o) G1 G2 G3).
Qed.
Lemma c2_hk_av : forall m m' a, c2_hkeep m m' ->
  gb_keep_at cx fp [(r, REG_SIZE)] a -> ~ (gF cx fp + GO_MAC <= a < gF cx fp + GO_MAC + 6) ->
  ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof. intros m m' a HKp G1 G2 G3. exact (HKp a G1 G2 G3). Qed.

(* read a spill slot (8 bytes, base atom 9 = sp1) back from the final symbolic state *)
Lemma c2_slot_read : forall E pc sr rl G (ms : machine_state) idx lo hi wlo whi cs off e v,
  st_ok_pi SEGS VAL E (mkSS pc sr rl None G) (restrict (w_H W3) ms) ->
  nth_error rl idx = Some (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9) = c_sp1 cx ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  gslot cx W3 ms off v.
Proof.
intros E pc sr rl G ms idx lo hi wlo whi cs off e v HS Hnth Hb Hin He Hv.
unfold gslot. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|exact Hv].
pose proof (st_ok_pi_region_nth E _ (restrict (w_H W3) ms) idx _ HS Hnth) as HR.
cbn [restrict ms_mem] in HR.
exact (field_of_region E _ 9%nat (c_sp1 cx) cs lo hi wlo whi off 8%N e v HR Hb Hin He
  ltac:(cbn [Z.of_N]; change (8 * 8) with 64; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.
(* read a MAC byte (1 byte, base atom 38 = F) back from the final symbolic state *)
Lemma c2_mac_read : forall E pc sr rl G (ms : machine_state) idx lo hi wlo whi cs off e v,
  st_ok_pi SEGS VAL E (mkSS pc sr rl None G) (restrict (w_H W3) ms) ->
  nth_error rl idx = Some (YP09.mkRegion (Some 38%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 38) = gF cx fp ->
  In (YP09.mkChunk off (CVal 1 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
  aview SEGS (w_H W3) (ms_mem ms) (gF cx fp + off) = Some v.
Proof.
intros E pc sr rl G ms idx lo hi wlo whi cs off e v HS Hnth Hb Hin He Hv.
apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms)); [|exact Hv].
pose proof (st_ok_pi_region_nth E _ (restrict (w_H W3) ms) idx _ HS Hnth) as HR.
cbn [restrict ms_mem] in HR.
exact (field_of_region E _ 38%nat (gF cx fp) cs lo hi wlo whi off 1%N e v HR Hb Hin He
  ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)).
Qed.


End g.


End d.
End c.
End b.
End a.

(* ======== the phase theorem: GI_K i -> GI_T 2 i ======== *)
Section Top.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis TFIND : treac_boxreg_find_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HZERO : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HRMB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Variable POST : bcx -> world SEGS -> config -> Prop.

(* the 64-byte margins of the two registered globals the case reads (ZERO, read_mac.base) *)
Lemma c2_marg : forall a n, In (a, n) BX_G -> IMG_LO + 64 <= a /\ a + n + 64 <= IMG_HI.
Proof. intros a n H. rewrite Forall_forall in HMRG. exact (HMRG (a, n) H). Qed.
Lemma HZ1 : IMG_LO + 64 <= VAL (A_OBJ 6).
Proof. exact (proj1 (c2_marg _ 6 ltac:(unfold BX_G; cbn [In]; tauto))). Qed.
Lemma HZ2 : VAL (A_OBJ 6) + 6 + 64 <= IMG_HI.
Proof. exact (proj2 (c2_marg _ 6 ltac:(unfold BX_G; cbn [In]; tauto))). Qed.
Lemma HM1 : IMG_LO + 64 <= VAL (A_OBJ 4).
Proof. exact (proj1 (c2_marg _ 5 ltac:(unfold BX_G; cbn [In]; tauto))). Qed.
Lemma HM2 : VAL (A_OBJ 4) + 5 + 64 <= IMG_HI.
Proof. exact (proj2 (c2_marg _ 5 ltac:(unfold BX_G; cbn [In]; tauto))). Qed.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* gb_keep_at membership by its named disjunct (sp side, input, frame, frame shadow, r); names no hypothesis. *)
Local Ltac c2_kat :=
  first [ (left; lia)
        | (right; left; lia)
        | (right; right; left; change (fs_frame_bytes GB_CID) with 512; lia)
        | (right; right; right; left; change (fs_frame_bytes GB_CID / 8) with 64; lia)
        | (right; right; right; right; apply Exists_cons_hd; cbn [fst snd]; unfold REG_SIZE; lia) ].
(* the 8 bytes at a + o are in the zone and off the MAC and cursor windows *)
Local Ltac c2mk_dom :=
  intros oo Hoo; try change (fs_frame_bytes GB_CID) with 512 in *;
  split; [ c2_kat | split; unfold GO_MAC, GO_PREV, REG_SIZE in *; lia ].

(* The head's writable windows: the cursor slots of the spill frame (sp1 = sp0 + d) and the MAC in the owned frame. *)
Lemma c2_awr_head : forall E cs1 cs2 rest FP bl0 blc ly own cx fp,
  bv_unsigned (ew E 9) = c_sp1 cx -> bv_unsigned (ew E 38) = gF cx fp ->
  spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256 ->
  In (GB_CID, fp) own -> frame_addr ly GB_CID fp = gF cx fp ->
  awr_ok E rest GB_STK (spZ (c_regs cx)) FP bl0 blc ly own ->
  awr_ok E (YP09.mkRegion (Some 9%nat) 0 0x98 0x88 0x98 cs1 :: YP09.mkRegion (Some 38%nat) 0 512 32 38 cs2 :: rest)
    GB_STK (spZ (c_regs cx)) FP bl0 blc ly own.
Proof.
intros E cs1 cs2 rest FP bl0 blc ly own cx fp H9 H38 Hsp Hown EF Hrest.
eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
  [reflexivity | lia | cbn; unfold GB_STK; lia | cbn; lia |].
eapply awr_ok_cons_gen with (n := 38%nat) (b := gF cx fp); [reflexivity | exact H38 | | exact Hrest].
intros a Ha. cbn in Ha. right; right; right. exists GB_CID, fp. split; [exact Hown|]. left.
unfold in_zr. rewrite EF. change (fs_frame_bytes GB_CID) with 512. cbn [fst snd]. lia.
Qed.

(* A run's memory frame as the head's keep: the run writes only the cursor and MAC windows. *)
Lemma c2_hk_of_frame : forall cx fp W3 r E rs m m',
  frame_of E rs m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a ->
     (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) \/ (gF cx fp + GO_MAC <= a < gF cx fp + GO_MAC + 6)) ->
  (forall a, gb_keep_at cx fp [(r, REG_SIZE)] a -> 0 <= a < 2 ^ 64) ->
  c2_hkeep cx fp W3 r m m'.
Proof.
intros cx fp W3 r E rs m m' HF Hw HGB a G1 G2 G3.
pose proof (HGB a G1) as Ha.
unfold aview, YP09.mbyte, mrestrict.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros Hin.
destruct (Hw a Ha Hin) as [Hc|Hc]; [exact (G3 Hc) | exact (G2 Hc)].
Qed.

Local Ltac c2h_awr F9 F38 EF :=
  lazymatch type of EF with _ = gF ?cx ?fp =>
  apply c2_awr_head with (cx := cx) (fp := fp);
    [cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
    | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
    | lia | left; reflexivity | exact EF | awr_ok_tac] end.

Lemma c2_inbyte_rng : forall cx pos j, 0 <= c2_inbyte cx pos j < 256.
Proof.
intros cx pos j. unfold c2_inbyte. destruct (_ <? _)%nat; [|lia].
pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat pos + j) (c_pl cx) (Z_to_bv 8 0))) as Hr.
change (bv_modulus 8) with 256 in Hr. lia.
Qed.
Lemma c2h_bytes_nth_rng : forall cx pos n, 0 <= nth n (c2h_bytes cx pos) 0 < 256.
Proof.
intros cx pos n. unfold c2h_bytes. destruct (Nat.lt_ge_cases n 6) as [Hn|Hn].
- rewrite (nth_indep _ 0 (c2_inbyte cx pos 0)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth. apply c2_inbyte_rng.
- rewrite nth_overflow by (rewrite length_map, length_seq; lia). lia.
Qed.
Lemma c2h_bytes_rng : forall cx pos, Forall (fun v => 0 <= v < 256) (c2h_bytes cx pos).
Proof.
intros cx pos. apply Forall_forall. intros v Hv. unfold c2h_bytes in Hv. apply in_map_iff in Hv as (j & <- & _).
apply c2_inbyte_rng.
Qed.

(* the run wrote only the cursor and MAC windows (the regions with a non-empty window) *)
Local Ltac c2h_wr F9 F38 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
  intros a Ha (rg & Hin & Hb); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.base_val YP09.r_base YP09.r_wlo YP09.r_whi ew ewset Nat.eqb] in Hb;
      first [ (rewrite F9, unsigned_lit_small in Hb by lia; left; lia)
            | (rewrite F38, unsigned_lit_small in Hb by lia; right; unfold GO_MAC; lia)
            | lia ] | ]);
  destruct Hin.
(* chain the head's keep through the last run's memory frame *)
Local Ltac c2h_keep HKA F9 F38 HGB :=
  lazymatch type of HKA with c2_hkeep ?cx ?fp ?W ?r ?m0 ?mO =>
  lazymatch goal with HFx : frame_of _ _ mO (ms_mem ?msN) |- _ =>
    let HK' := fresh "HKA" in
    assert (HK' : c2_hkeep cx fp W r m0 (ms_mem msN))
      by (apply (c2_hk_trans cx fp W r m0 mO (ms_mem msN) HKA HKA);
          apply (c2_hk_of_frame cx fp W r _ _ _ _ HFx); [c2h_wr F9 F38 | exact HGB]);
    clear HKA HFx; rename HK' into HKA
  end end;
  repeat match goal with H : mem_grows _ _ |- _ => clear H end.

(* ---- path A (op & 4 = 0): the memcpy of read_mac.base into mac, then mac[5] ---- *)
Definition c2_mac5 : list YP09.chunk :=
  [YP09.mkChunk 32 (CVal 1 (SLit 0)); YP09.mkChunk 33 (CVal 1 (SLit 64)); YP09.mkChunk 34 (CVal 1 (SLit 171));
   YP09.mkChunk 35 (CVal 1 (SLit 0)); YP09.mkChunk 36 (CVal 1 (SLit 0))].

(* A frame byte is never an image byte (AR's client/image law), so the frame and a read-only global are apart. *)
Lemma c2_frame_rom_disj : forall ly S (W : world SEGS) mem md cx fp a l,
  AR SEGS B ly S W mem md -> In (GB_CID, fp) (frames S) -> frame_addr ly GB_CID fp = gF cx fp ->
  SnprintfDef.asn_rom_bytes SEGS B a l ->
  forall d n, gF cx fp <= d -> d + n <= gF cx fp + 512 -> 0 < n -> n <= Z.of_nat (length l) ->
  d + n <= a \/ a + n <= d.
Proof.
intros ly S W mem md cx fp a l HAR Hin EF HRB d n Hd1 Hd2 Hn Hnl.
destruct (Z_le_gt_dec (d + n) a) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (a + n) d) as [H'|H']; [right; exact H'|].
exfalso.
assert (Hp1 : d <= Z.max d a < d + n) by lia.
assert (Hp2 : a <= Z.max d a < a + n) by lia.
destruct (HRB (Z.max d a - a) ltac:(lia)) as (Hrom & _).
replace (a + (Z.max d a - a)) with (Z.max d a) in Hrom by lia.
destruct (al_client_img _ _ LAWS _ _ _ _ _ (Z.max d a) HAR) as [_ Hni].
{ right; left. exists GB_CID, fp. split; [exact Hin|]. rewrite EF. change (fs_frame_bytes GB_CID) with 512. lia. }
apply Hni. destruct Hrom as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
Qed.

(* the windows after the memcpy: mac[5] in the re-added frame, then the cursor slots *)
Lemma c2_awr_head2 : forall E cs1 cs2 rest FP bl0 blc ly own cx fp,
  bv_unsigned (ew E 9) = c_sp1 cx -> bv_unsigned (ew E 38) = gF cx fp ->
  spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256 ->
  In (GB_CID, fp) own -> frame_addr ly GB_CID fp = gF cx fp ->
  awr_ok E rest GB_STK (spZ (c_regs cx)) FP bl0 blc ly own ->
  awr_ok E (YP09.mkRegion (Some 38%nat) 0 512 37 38 cs2 :: YP09.mkRegion (Some 9%nat) 0 0x98 0x88 0x98 cs1 :: rest)
    GB_STK (spZ (c_regs cx)) FP bl0 blc ly own.
Proof.
intros E cs1 cs2 rest FP bl0 blc ly own cx fp H9 H38 Hsp Hown EF Hrest.
eapply awr_ok_cons_gen with (n := 38%nat) (b := gF cx fp); [reflexivity | exact H38 | |].
{ intros a Ha. cbn in Ha. right; right; right. exists GB_CID, fp. split; [exact Hown|]. left.
  unfold in_zr. rewrite EF. change (fs_frame_bytes GB_CID) with 512. cbn [fst snd]. lia. }
eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
  [reflexivity | lia | cbn; unfold GB_STK; lia | cbn; lia | exact Hrest].
Qed.

Local Ltac c2h_awr2 F9 F38 EF :=
  lazymatch type of EF with _ = gF ?cx ?fp =>
  apply c2_awr_head2 with (cx := cx) (fp := fp);
    [cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
    | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
    | lia | left; reflexivity | exact EF | awr_ok_tac] end.

(* a call that writes only inside the MAC window and below sp1 keeps the head's zone *)
Lemma c2_hk_call : forall cx fp W3 r m m' d n,
  gF cx fp + GO_MAC <= d -> d + n <= gF cx fp + GO_MAC + 6 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (c_sp1 cx - ESTACK <= a < c_sp1 cx) ->
     aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  (forall a, gb_keep_at cx fp [(r, REG_SIZE)] a -> 0 <= a < 2 ^ 64 /\ ~ (c_sp1 cx - ESTACK <= a < c_sp1 cx)) ->
  c2_hkeep cx fp W3 r m m'.
Proof.
intros cx fp W3 r m m' d n Hd1 Hd2 Hout HZ a G1 G2 G3.
destruct (HZ a G1) as [Ha Hs]. apply Hout; [exact Ha | lia | exact Hs].
Qed.

Lemma c2_hk_gshadow : forall cx fp W3 r (ms ms' : machine_state),
  c2_hkeep cx fp W3 r (ms_mem ms) (ms_mem ms') ->
  gSH cx fp + 64 <= gF cx fp \/ gF cx fp + 512 <= gSH cx fp -> gSH cx fp + 64 <= c_sp1 cx ->
  gshadow cx fp W3 ms GSH_it -> gshadow cx fp W3 ms' GSH_it.
Proof.
intros cx fp W3 r ms ms' HKp HF HC HSH ii Hii. change (length GSH_it) with 52%nat in Hii.
rewrite (HKp (gSH cx fp + Z.of_nat ii)).
- apply HSH. change (length GSH_it) with 52%nat. exact Hii.
- right; right; right; left. change (fs_frame_bytes GB_CID / 8) with 64. lia.
- unfold GO_MAC. lia.
- lia.
Qed.

(* the head's shadow entries (the MAC window and the k input bytes) at any memory that keeps their shadow *)
Lemma c2h_sh_gen : forall cx fp pos kk E (W3 : world SEGS) m,
  ew E 18 = Z_to_bv 64 SHADOW_OFF -> ew E 38 = Z_to_bv 64 (gF cx fp) -> ew E 32 = Z_to_bv 64 (c_p cx + pos) ->
  0 <= gF cx fp < 2 ^ 64 -> 0 <= c_p cx + pos < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (gF cx fp + 32) 6 ->
  (gF cx fp + 512 <= kLowShadowBeg \/ kHighMemBeg <= gF cx fp) ->
  (kk <> 0%nat -> range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (c_p cx + pos) (Z.of_nat kk) /\
     (c_p cx + pos + Z.of_nat kk <= kLowShadowBeg \/ kHighMemBeg <= c_p cx + pos)) ->
  sh_ok SEGS c2_Bx (c2h_SH kk) E (mrestrict (w_H W3) m).
Proof.
intros cx fp pos kk E W3 m A18 A38 A32 V38 V32 HRA HAF HIN.
assert (UB : U E c2_Bx = SHADOW_OFF) by (unfold c2_Bx; apply (U_atom E 18 _ A18); unfold SHADOW_OFF; lia).
unfold sh_ok, c2h_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UB, (U_atom E 38 _ A38) by lia. rewrite <- (aview_rd_of SEGS). split.
  + replace (38 - 32) with 6 by lia. exact HRA.
  + intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
- unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UB, (U_atom E 32 _ A32) by lia. rewrite <- (aview_rd_of SEGS).
  destruct (Nat.eq_dec kk 0) as [Hk0 | Hk0].
  + subst kk. cbn [Z.of_nat]. split; [intros x Hx; lia | intros a Ha; lia].
  + destruct (HIN Hk0) as [HR HA]. split.
    * replace (c_p cx + pos + 0) with (c_p cx + pos) by lia. replace (Z.of_nat kk - 0) with (Z.of_nat kk) by lia.
      exact HR.
    * intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
      unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* the frame, put back after the memcpy: mac[0 .. 4] as the copied bytes, mac[5] writable *)
Lemma c2_frameA_ok : forall cx fp E (W3 : world SEGS) m ly S md,
  AR SEGS B ly S W3 m md -> In (GB_CID, fp) (frames S) -> frame_addr ly GB_CID fp = gF cx fp ->
  ew E 38 = Z_to_bv 64 (gF cx fp) -> 4096 <= gF cx fp -> gF cx fp + 512 <= 2 ^ 63 ->
  (forall j, 0 <= j < 5 -> aview SEGS (w_H W3) m (gF cx fp + GO_MAC + j) = Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0)) ->
  YP09.region_ok SEGS E (mrestrict (w_H W3) m) (c2_frame c2_mac5 37 38).
Proof.
intros cx fp E W3 m ly S md HAR Hfin EF A38 HF0 HFc Hm.
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (_ & _ & Hpres & _).
rewrite EF in Hpres. change (fs_frame_bytes GB_CID) with 512 in Hpres.
unfold YP09.region_ok, c2_frame. cbv zeta.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
rewrite (c2_U _ _ _ A38) by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
unfold c2_mac5. repeat apply Forall_cons; try apply Forall_nil; (eapply c2_chunk1; [reflexivity |]).
- replace (gF cx fp + 32) with (gF cx fp + GO_MAC + 0) by (unfold GO_MAC; lia). exact (Hm 0 ltac:(lia)).
- replace (gF cx fp + 33) with (gF cx fp + GO_MAC + 1) by (unfold GO_MAC; lia). exact (Hm 1 ltac:(lia)).
- replace (gF cx fp + 34) with (gF cx fp + GO_MAC + 2) by (unfold GO_MAC; lia). exact (Hm 2 ltac:(lia)).
- replace (gF cx fp + 35) with (gF cx fp + GO_MAC + 3) by (unfold GO_MAC; lia). exact (Hm 3 ltac:(lia)).
- replace (gF cx fp + 36) with (gF cx fp + GO_MAC + 4) by (unfold GO_MAC; lia). exact (Hm 4 ltac:(lia)).
Qed.

(* Build c2_FI at the exit (0x80614): registers/cursor/mac from the exit state, the rest kept from the entry. *)
Lemma c2_mkFI : forall cx fp k ly3 S3 W3 i r q bs (mse msF : machine_state) (md md' : Model) (M : list byte),
  gb_base B MT cx -> frames S3 = [(GB_CID, fp)] -> gblk1 B cx ly3 S3 r -> Boxreg.boxreg_inv bs ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem mse) md k ->
  gsaved cx W3 mse -> gshadow cx fp W3 mse GSH_it ->
  rdword (aview SEGS (w_H W3) (ms_mem mse)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) ->
  gslots_fr cx fp W3 mse -> gslots_r cx fp W3 mse r (Boxreg.bx_fabric bs) -> gslot cx W3 mse 0x68 i ->
  greg B ly3 S3 W3 mse r bs -> gprev cx fp W3 mse bs ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem mse)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  c2_hkeep cx fp W3 r (ms_mem mse) (ms_mem msF) ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem msF) md' k ->
  msF = mkst (ms_regs msF) (w64 (BASE + GP_F)) (ms_mem msF) (seg_rom SEGS) ->
  getr (ms_regs msF) 2 = w64 (c_sp1 cx) -> getr (ms_regs msF) 8 = w64 (spZ (c_regs cx)) ->
  getr (ms_regs msF) 9 = w64 (c_sp1 cx) -> getr (ms_regs msF) 3 = getr (c_regs cx) 3 ->
  getr (ms_regs msF) 4 = getr (c_regs cx) 4 -> getr (ms_regs msF) 18 = w64 SHADOW_OFF ->
  getr (ms_regs msF) 24 = w64 (gSH cx fp) ->
  getr (ms_regs msF) 20 = w64 r -> getr (ms_regs msF) 21 = w64 (gF cx fp + GO_MAC) ->
  getr (ms_regs msF) 25 = w64 (Boxreg.bx_fabric bs) ->
  gcursor cx W3 msF q -> length M = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + GO_MAC + j) =
     Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) ->
  c2_FI B cx fp k ly3 S3 W3 i r q bs msF md' M.
Proof.
intros cx fp k ly3 S3 W3 i r q bs mse msF md md' M HB HFR HBLK HINV HJe HSVe HSHe HFLe HSFRe HSLRe HS68e
  HREGe HPREVe HINe HKP HJF HmsF G2 G8 G9 G3 G4 G18 G24 R20 R21 R25 Hcur HML HMb.
pose proof (c2_geo B MT LAWS cx fp k ly3 S3 W3 r HB HFR HBLK mse md HJe)
  as ((Hal16 & Hlo & Hhi & Hsp1 & Hsp1al) & (HF0 & HFc & HFia & HFal & HSHeq) & (Hr16 & Hr4096 & Hrc & Hria)
      & DRF & Hinp).
pose proof asan_consts as (Hac & _).
pose proof HJe as (HARe & _).
assert (Hrblk : In (r, REG_SIZE) (ablocks B ly3 S3)) by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
assert (HINW : c_n cx = 0 \/
  (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
  by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc & _ & DPF & _)]; [left; exact Hn0 | right; repeat split; assumption]).
clear Hinp.
assert (Hgd : 0 <= gF cx fp / 8 <= 17592186044416).
{ split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | unfold SHADOW_OFF in *; lia]]. }
assert (HSHh : gSH cx fp + 64 <= c_sp1 cx) by (rewrite HSHeq; unfold SHADOW_OFF in *; lia).
assert (HSHF : gSH cx fp + 64 <= gF cx fp \/ gF cx fp + 512 <= gSH cx fp).
{ rewrite HSHeq. pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)) as Hmd. unfold in_app in HFia.
  unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *. lia. }
clear HFia Hria.
assert (HGSH : forall n, gSH cx fp <= n < gSH cx fp + 64 -> gb_keep_at cx fp [(r, REG_SIZE)] n)
  by (intros n Hn; right; right; right; left; change (fs_frame_bytes GB_CID / 8) with 64; lia).
assert (HGframe : forall n, gF cx fp <= n < gF cx fp + 512 -> gb_keep_at cx fp [(r, REG_SIZE)] n)
  by (intros n Hn; right; right; left; change (fs_frame_bytes GB_CID) with 512; lia).
assert (HGr : forall n, r <= n < r + 288 -> gb_keep_at cx fp [(r, REG_SIZE)] n)
  by (intros n Hn; right; right; right; right; apply Exists_cons_hd; cbn [fst snd]; unfold REG_SIZE; lia).
assert (HGin : forall n, c_p cx <= n < c_p cx + c_n cx -> gb_keep_at cx fp [(r, REG_SIZE)] n)
  by (intros n Hn; right; left; lia).
(* transport an rdword fact of ms e to ms F *)
assert (HK := HKP).
set (m0 := ms_mem mse) in *. set (m1 := ms_mem msF) in *.
assert (TRr : forall a v (which : forall o, 0 <= o < 8 -> gb_keep_at cx fp [(r, REG_SIZE)] (a + o) /\
    ~ (gF cx fp + GO_MAC <= a + o < gF cx fp + GO_MAC + 6) /\ ~ (c_sp1 cx + 0x88 <= a + o < c_sp1 cx + 0x98)),
    rdword (aview SEGS (w_H W3) m0) a = Some v -> rdword (aview SEGS (w_H W3) m1) a = Some v)
  by (intros a v which Hr; exact (c2_hk_rd cx fp W3 r m0 m1 a v HK which Hr)).
assert (TRa : forall a (which : gb_keep_at cx fp [(r, REG_SIZE)] a /\
    ~ (gF cx fp + GO_MAC <= a < gF cx fp + GO_MAC + 6) /\ ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98)),
    aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
  by (intros a (w1 & w2 & w3); exact (c2_hk_av cx fp W3 r m0 m1 a HK w1 w2 w3)).
(* assemble c2_FI *)
assert (Hpc2 : ms_pc_val msF = w64 (BASE + GP_F)) by (rewrite HmsF at 1; reflexivity).
assert (Hrv2 : ms_resv msF = None) by (rewrite HmsF at 1; reflexivity).
assert (Hsv2 : ms_svc_pending msF = None) by (rewrite HmsF at 1; reflexivity).
assert (Hrom2 : ms_rom msF = seg_rom SEGS) by (rewrite HmsF at 1; reflexivity).
assert (Hfrr2 : ms_fregs msF = fp_regs) by (rewrite HmsF at 1; reflexivity).
assert (Hfc2 : ms_fcsr msF = fp_csr) by (rewrite HmsF at 1; reflexivity).
unfold c2_FI.
split.
{ unfold gb_body.
  split; [exact Hpc2|]. split; [exact Hrv2|]. split; [exact Hsv2|]. split; [exact Hrom2|].
  split; [exact Hfrr2|]. split; [exact Hfc2|].
  split; [unfold gregs; repeat split; assumption|].
  split.
  { destruct HSVe as [Hra Hsj]. split.
    - apply TRr; [c2mk_dom|]. exact Hra.
    - intros j Hj. apply TRr; [c2mk_dom|]. exact (Hsj j Hj). }
  split.
  { intros ii Hii. unfold gshadow in HSHe. change (length GSH_it) with 52%nat in Hii.
    rewrite TRa; [apply HSHe; change (length GSH_it) with 52%nat; exact Hii|].
    repeat split; [apply HGSH; lia | unfold GO_MAC; lia | lia]. }
  split; [reflexivity|].
  split.
  { apply TRr; [c2mk_dom|]. exact HFLe. }
  split.
  { destruct HSFRe as (A18 & A28 & A70 & A78 & A80). unfold gslots_fr, gslot in *.
    repeat split;
      (apply TRr; [c2mk_dom | eassumption]). }
  { intros j Hj. unfold garr8 in HINe. destruct (HINe j Hj) as [Hv Hb]. split; [|exact Hb].
    assert (Ha : aview SEGS (w_H W3) m1 (c_p cx + Z.of_nat j) = Some (nth j (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0)).
    { rewrite TRa; [exact (aview_of_val_mem1 SEGS (w_H W3) m0 _ _ Hv Hb)|].
      rewrite length_map in Hj. unfold c_n in *.
      repeat split; [apply HGin; lia | unfold GO_MAC in *; lia | lia]. }
    exact (proj1 (val_mem1_of_aview SEGS (w_H W3) m1 _ _ Ha)). } }
split; [exact HJF|].
split.
{ unfold greg in HREGe |- *. destruct HREGe as (Hin & Hlen & Hb). split; [exact Hrblk|]. split; [exact Hlen|].
  intros ii Hii. rewrite TRa; [apply Hb; exact Hii|].
  unfold REG_SIZE in *. repeat split; [apply HGr; lia | unfold GO_MAC in *; lia | lia]. }
split.
{ unfold gprev in HPREVe |- *. intros ii Hii. rewrite TRa; [apply HPREVe; exact Hii|].
  unfold REG_SIZE, GO_PREV, GO_MAC in *. try change (fs_frame_bytes GB_CID) with 512 in *.
  repeat split; [apply HGframe; lia | lia | lia]. }
split.
{ destruct HSLRe as (A10 & A20 & A38 & A40 & A50 & A60). unfold gslots_r, gslot in *.
  repeat split; (apply TRr; [c2mk_dom | eassumption]). }
split; [exact Hcur|].
split.
{ unfold gslot in HS68e |- *. apply TRr; [c2mk_dom|]. exact HS68e. }
split; [exact R20|]. split; [exact R21|]. split; [exact R25|].
split; [exact HML|]. exact HMb.
Qed.



(* a byte atom, zero-extended *)
Lemma c2_den_zext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SExt false 8 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U, U_SExt. cbv beta iota.
rewrite U_SOff, H, unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite (zcanon_id v) by (unfold M64; lia). change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by lia. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

(* the end of the head (0x80614): from the exit state's facts, c2_mkFI then c2_tail *)
Lemma c2_fin : forall i cx fp k acc ly3 S3 W3 r q bs (mse msF : machine_state) (md md' : Model) (vals : list Z),
  gb_from B MT POST (GI_K B MT i) -> gb_base B MT cx -> frames S3 = [(GB_CID, fp)] -> gblk1 B cx ly3 S3 r ->
  Boxreg.boxreg_inv bs -> mo_le MT (c_S cx) S3 acc -> k <= 1 + 2 * i -> acc <= GB_A MT i -> 0 <= i < 64 ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem mse) md k ->
  gsaved cx W3 mse -> gshadow cx fp W3 mse GSH_it ->
  rdword (aview SEGS (w_H W3) (ms_mem mse)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) ->
  gslots_fr cx fp W3 mse -> gslots_r cx fp W3 mse r (Boxreg.bx_fabric bs) -> gslot cx W3 mse 0x68 i ->
  greg B ly3 S3 W3 mse r bs -> gprev cx fp W3 mse bs ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem mse)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  c2_hkeep cx fp W3 r (ms_mem mse) (ms_mem msF) ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem msF) md' k ->
  msF = mkst (ms_regs msF) (w64 (BASE + GP_F)) (ms_mem msF) (seg_rom SEGS) ->
  getr (ms_regs msF) 2 = w64 (c_sp1 cx) -> getr (ms_regs msF) 8 = w64 (spZ (c_regs cx)) ->
  getr (ms_regs msF) 9 = w64 (c_sp1 cx) -> getr (ms_regs msF) 3 = getr (c_regs cx) 3 ->
  getr (ms_regs msF) 4 = getr (c_regs cx) 4 -> getr (ms_regs msF) 18 = w64 SHADOW_OFF ->
  getr (ms_regs msF) 24 = w64 (gSH cx fp) ->
  getr (ms_regs msF) 20 = w64 r -> getr (ms_regs msF) 21 = w64 (gF cx fp + GO_MAC) ->
  getr (ms_regs msF) 25 = w64 (Boxreg.bx_fabric bs) ->
  gcursor cx W3 msF q -> length vals = 6%nat -> Forall (fun v => 0 <= v < 256) vals ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + GO_MAC + j) = Some (nth (Z.to_nat j) vals 0)) ->
  SRr SEGS W3 (mkCfg msF md') (POST cx).
Proof.
intros i cx fp k acc ly3 S3 W3 r q bs mse msF md md' vals HK HB HFR HBLK HINV HMO Hk Hacc Hi64 HJe HSVe HSHe HFLe
  HSFRe HSLRe HS68e HREGe HPREVe HINe HKP HJF HmsF G2 G8 G9 G3 G4 G18 G24 R20 R21 R25 Hcur Hlen Hrng HMv.
apply (c2_tail B MT LAWS cx fp k acc ly3 S3 W3 i r q bs HB HFR HBLK HINV POST MTL HK HMO Hk Hacc Hi64 HGLOB HISV
  HZERO HZ1 HZ2 TFIND ABCMP msF md' (map (fun v => Z_to_bv 8 v) vals)).
apply (c2_mkFI cx fp k ly3 S3 W3 i r q bs mse msF md md' _ HB HFR HBLK HINV HJe HSVe HSHe HFLe HSFRe HSLRe HS68e
  HREGe HPREVe HINe HKP HJF HmsF G2 G8 G9 G3 G4 G18 G24 R20 R21 R25 Hcur).
- rewrite length_map. exact Hlen.
- intros j Hj. rewrite (HMv j Hj). f_equal.
  rewrite (map_nth (fun v => Z_to_bv 8 v) vals 0 (Z.to_nat j)), Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite Z.mod_small; [reflexivity|].
  rewrite Forall_forall in Hrng. apply Hrng. apply nth_In. lia.
Qed.

Lemma c2h_bytes_out : forall cx pos j, 0 <= pos -> (j < 6)%nat -> c_n cx <= pos + Z.of_nat j ->
  nth j (c2h_bytes cx pos) 0 = 0.
Proof.
intros cx pos j Hp Hj Hn. unfold c2h_bytes.
rewrite (nth_indep _ 0 (c2_inbyte cx pos 0)) by (rewrite length_map, length_seq; lia).
rewrite map_nth, seq_nth by lia. cbn [Nat.add]. unfold c2_inbyte.
destruct (Nat.ltb_spec (Z.to_nat pos + j) (length (c_pl cx))) as [H|H]; [unfold c_n in Hn; lia | reflexivity].
Qed.

Lemma c2_valsA_rng : forall cx pos n, 0 <= nth n [0; 64; 171; 0; 0; nth 0 (c2h_bytes cx pos) 0] 0 < 256.
Proof.
intros cx pos n. destruct n as [|[|[|[|[|[|n]]]]]]; cbn [nth]; try lia; [apply c2h_bytes_nth_rng | destruct n; lia].
Qed.

Theorem gb_case2 : forall i, gb_from B MT POST (GI_K B MT i) -> gb_from B MT POST (GI_T B MT 2 i).
Proof.
intros i HK cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & bs & pos & op & HBODY & Hi64 & Hk & Hacc & HBLK & HREG & HPREV & HINV & Hop & Hop3
  & R20 & R22 & R25 & R26 & HSLR & HCUR & HS68 & _).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4 & G18 & G24)
  & HSV & HSH & Hlen & HFL & HSFR & HIN).
pose proof HCUR as (Hpos & HC88 & HC90).
assert (Hcn : 0 <= c_n cx < 2 ^ 26)
  by (pose proof HB as (_ & _ & _ & Hinp & _); unfold c_n in *; destruct Hinp as [(H0 & _) | (H0 & _)]; lia).
set (kk := Z.to_nat (Z.min 6 (c_n cx - pos))).
assert (Hkm : Z.of_nat kk = Z.min 6 (c_n cx - pos)) by (unfold kk; rewrite Z2Nat.id; [reflexivity | lia]).
assert (Hk6 : (kk <= 6)%nat) by (unfold kk; lia).
assert (Hbl : length (c2h_bytes cx pos) = 6%nat) by (unfold c2h_bytes; rewrite length_map, length_seq; reflexivity).
destruct (c2h_seat B MT LAWS cx fp k ly3 S3 W3 i r pos bs HB HFR HBLK HINV ms3 md3 HJ HREG
  (c2h_bytes cx pos) Hbl G2 G9 G18 R20 R25 HSFR HSLR HCUR HS68 Hi64 (proj2 Hcn) HSH HIN kk eq_refl Hk6 Hkm
  Hpc Hresv Hsvc Hrom Hfr Hfcsr) as [HS SHOK].
pose proof (c2_atoms cx fp i r pos bs ms3 (c2h_bytes cx pos) Hbl G2 G9 G18 R20 R25 Hi64) as AT.
destruct AT as (F9 & F2 & F18 & F20 & F25 & F32 & F33 & F34 & F35 & F36 & F37 & F38).
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
assert (F3 : ew (c2_E cx fp i r pos bs ms3 (c2h_bytes cx pos)) 3 = w64 (as_gp B))
  by (rewrite (c2_ew_reg cx fp i r pos bs ms3 _ 3 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew (c2_E cx fp i r pos bs ms3 (c2h_bytes cx pos)) 4 = w64 (as_tp B))
  by (rewrite (c2_ew_reg cx fp i r pos bs ms3 _ 4 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew (c2_E cx fp i r pos bs ms3 (c2h_bytes cx pos)) 8 = w64 (spZ (c_regs cx)))
  by (rewrite (c2_ew_reg cx fp i r pos bs ms3 _ 8 8%bv eq_refl); exact G8).
assert (F22 : ew (c2_E cx fp i r pos bs ms3 (c2h_bytes cx pos)) 22 = w64 op)
  by (rewrite (c2_ew_reg cx fp i r pos bs ms3 _ 22 22%bv eq_refl); exact R22).
assert (F24 : ew (c2_E cx fp i r pos bs ms3 (c2h_bytes cx pos)) 24 = w64 (gSH cx fp))
  by (rewrite (c2_ew_reg cx fp i r pos bs ms3 _ 24 24%bv eq_refl); exact G24).
assert (F26 : ew (c2_E cx fp i r pos bs ms3 (c2h_bytes cx pos)) 26 = w64 (Boxreg.bx_n bs))
  by (rewrite (c2_ew_reg cx fp i r pos bs ms3 _ 26 26%bv eq_refl); exact R26).
assert (HEI : img_env VAL A_LIM (c2_E cx fp i r pos bs ms3 (c2h_bytes cx pos))) by (unfold c2_E; apply Eimg_env).
pose proof (c2_byte_atom cx fp i r pos bs ms3 (c2h_bytes cx pos) Hbl Hi64) as FB.
remember (c2_E cx fp i r pos bs ms3 (c2h_bytes cx pos)) as E eqn:HE.
unfold w64 in F2, F3, F4, F8, F9, F18, F20, F22, F24, F25, F26, F32, F33, F34, F35, F36, F37, F38.
clearbody kk.
pose proof (c2_geo B MT LAWS cx fp k ly3 S3 W3 r HB HFR HBLK ms3 md3 HJ)
  as ((Hal16 & Hlo & Hhi & Hsp1 & Hsp1al) & (HF0 & HFc & HFia & HFal & HSHeq) & (Hr16 & Hr4096 & Hrc & Hria)
      & DRF & Hinp).
pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
pose proof asan_consts as (Hac & _).
assert (HGB : forall a, gb_keep_at cx fp [(r, REG_SIZE)] a -> 0 <= a < 2 ^ 64).
{ assert (Hgd : 0 <= gF cx fp / 8 <= 17592186044416)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | unfold SHADOW_OFF in *; lia]]).
  intros a [H|[H|[H|[H|H]]]].
  - lia.
  - destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpce & _)]; lia.
  - change (fs_frame_bytes GB_CID) with 512 in H. lia.
  - change (fs_frame_bytes GB_CID / 8) with 64 in H. rewrite HSHeq in H. unfold SHADOW_OFF in *. lia.
  - apply Exists_cons in H as [H|H]; [cbn [fst snd] in H; unfold REG_SIZE in H; lia | inversion H]. }
pose proof (c2_hk_refl cx fp W3 r (ms_mem ms3)) as HKA.
pose proof HJ as HJ0.
pose proof (c2_nums B MT LAWS cx fp k ly3 S3 W3 i r HB HFR HBLK ms3 md3 HJ (c2h_bytes cx pos) Hbl Hi64)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HFapp & N9 & N10 & N11 & N12 & N13 & N14 & N15).
assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (Hgd : 0 <= gF cx fp / 8 <= 17592186044416)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | unfold SHADOW_OFF in *; lia]]).
assert (HSHh : gSH cx fp + 64 <= c_sp1 cx) by (rewrite HSHeq; unfold SHADOW_OFF in *; lia).
assert (HSHF : gSH cx fp + 64 <= gF cx fp \/ gF cx fp + 512 <= gSH cx fp).
{ rewrite HSHeq. pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)) as Hmd.
  unfold kHighMemBeg, kLowShadowBeg, SHADOW_OFF in *. lia. }
assert (HGB2 : forall a, gb_keep_at cx fp [(r, REG_SIZE)] a -> 0 <= a < 2 ^ 64 /\ ~ (c_sp1 cx - ESTACK <= a < c_sp1 cx)).
{ intros a Ha. split; [exact (HGB a Ha)|]. unfold ESTACK.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpce & _)]; lia.
  - change (fs_frame_bytes GB_CID) with 512 in H. lia.
  - change (fs_frame_bytes GB_CID / 8) with 64 in H. rewrite HSHeq in H. unfold SHADOW_OFF in *. lia.
  - apply Exists_cons in H as [H|H]; [cbn [fst snd] in H; unfold REG_SIZE in H; lia | inversion H]. }
assert (V36 : 0 <= shadow_of_addr SHADOW_OFF (r + 280) < 2 ^ 64) by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
assert (HINW : c_n cx = 0 \/ (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\
   (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx) /\
   (c_p cx + c_n cx <= kLowShadowBeg \/ kHighMemBeg <= c_p cx))).
{ destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpce & Hpia & DPF & _)]; [left; exact Hn0 | right].
  unfold in_app in Hpia. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. repeat split; lia. }
assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|].
  destruct Hal16 as [q1 Hq1]. apply Z.mod_divide in Hsp1al; [|lia]. destruct Hsp1al as [q2 Hq2]. exists (2 * q2 - q1). lia. }
pose proof HM1 as HM1'. pose proof HM2 as HM2'. unfold IMG_HI in HM2'.
destruct kk as [|[|[|[|[|[|[|kk']]]]]]]; [| | | | | | | exfalso; lia].
- (* kk = 0 *)
  paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
  c2h_keep HKA F9 F38 HGB.
  psrr_branch_tok RUN BR HS SHOK c2_span.
  + (* op & 4 <> 0: the six-byte loop *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    psrr_branch_tok RUN BR HS SHOK c2_span.
    2: { exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite F33, unsigned_lit_small in Hc by lia.
         match type of Hc with context [Z_to_bv 64 (c_n cx - pos + ?x)] => replace (c_n cx - pos + x) with 0 in Hc by lia end.
         vm_compute in Hc. discriminate. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 0 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 0) bs ms3 msF md3 _ (c2h_bytes cx pos) HK HB HFR HBLK HINV HMO
      Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * exact Hbl.
    * apply c2h_bytes_rng.
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      lazymatch goal with |- aview _ _ _ (_ + (32 + ?jz)) = _ =>
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 1%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB (Z.to_nat jz) ltac:(lia)) | apply c2h_bytes_nth_rng]
                | cbn [sv_denot]; rewrite (c2h_bytes_out cx pos (Z.to_nat jz)) by lia; reflexivity ]
        | apply c2h_bytes_nth_rng ]) end.
  + (* op & 4 = 0: memcpy (read_mac.base, 5 bytes), then one input byte *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msT end.
    pose proof (c2_hk_gshadow cx fp W3 r ms3 msT HKA HSHF HSHh HSH) as HSHT.
    pmkst HS.
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
    pose proof HJ as (HART & _).
    pose proof (c2_rom B MT cx W3 HB (VAL (A_OBJ 4)) [0; 64; 171; 0; 0] _ _ _ _ _ _ HRMB HJ) as HRT.
    destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem msT) _ (VAL (A_OBJ 4)) 5 (VAL (A_OBJ 4)) 5
      HGLOB ltac:(unfold BX_G; right; right; left; reflexivity) HISV HART ltac:(lia) ltac:(lia) ltac:(lia) HM1 HM2)
      as [HXra HXhv].
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
    eapply SRr_bind;
    [ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA BS___asan_memcpy) AMEMCPY W3 rg mm
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (gF cx fp + GO_MAC) (VAL (A_OBJ 4)) 5 (c_sp1 cx - spZ (c_regs cx)) _ HJ);
      [ rewrite Ra0, F38, unsigned_lit_small by lia; reflexivity
      | rewrite Ra1; change 245%nat with (A_OBJ 4); apply (img_env_atomP E (A_OBJ 4) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia
      | rewrite Ra2; reflexivity
      | lia | unfold GO_MAC; lia | unfold GO_MAC; lia
      | unfold spZ at 1; rewrite Rsp, F2, unsigned_lit_small by lia; lia
      | exact Ho16
      | lia
      | unfold ESTACK, GB_STK; lia
      | rewrite Rgp, F3; reflexivity
      | rewrite Rtp, F4; reflexivity
      | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; right; right; exists GB_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; rewrite EF;
          change (fs_frame_bytes GB_CID) with 512; cbn [fst snd]; unfold GO_MAC in *; lia
        | unfold ESTACK, GO_MAC in *; lia ]
      | unfold amem_range; unfold in_app in HFia; unfold GO_MAC, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *; lia
      | pose proof (gb_mac_ra B MT LAWS cx fp W3 msT ly3 S3 _ k HB HJ HFR 0 5 HSHT ltac:(lia) ltac:(lia)) as Hra;
        rewrite Z.add_0_r in Hra; exact Hra
      | intros _; apply (shadow_hull_vis_of_frame _ _ LAWS _ _ _ _ _ GB_CID fp _ _ HART ltac:(rewrite HFR; left; reflexivity));
        try rewrite EF; change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia;
            rewrite (HRT (a - VAL (A_OBJ 4)) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)); discriminate
          | unfold spZ at 1 2; rewrite Rsp, F2, unsigned_lit_small by lia; unfold ESTACK; lia ] |];
        split; [ exact (c2_frame_rom_disj ly3 S3 W3 _ _ cx fp _ _ HART Hfin EF HRMB (gF cx fp + GO_MAC) 5
                   ltac:(unfold GO_MAC; lia) ltac:(unfold GO_MAC; lia) ltac:(lia) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)) |];
        split; [ unfold amem_range, kLowMemEnd; lia |];
        split; [ exact HXra | intros _; exact HXhv ] ]
    | ] end.
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout & Hpres2).
    assert (HKA2 : c2_hkeep cx fp W3 r (ms_mem ms3) mem2).
    { apply (c2_hk_trans cx fp W3 r _ (ms_mem msT) mem2 HKA HKA).
      apply (c2_hk_call cx fp W3 r (ms_mem msT) mem2 (gF cx fp + GO_MAC) 5); [lia | lia | | exact HGB2].
      intros a Ha H1 H2. apply Hout; [exact Ha | exact H1 | lia]. }
    clear HKA. rename HKA2 into HKA.
    assert (HM5 : forall j, 0 <= j < 5 -> aview SEGS (w_H W3) mem2 (gF cx fp + GO_MAC + j) =
      Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0)).
    { intros j Hj. rewrite (Heff j Hj). exact (HRT j ltac:(cbn; lia)). }
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
    jafter_call_keep_pi HS 45%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 2; 3]%nat HS2.
    match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val];
        rewrite ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
        intros a Ha;
        first [ (apply (mbyte_of_aview SEGS); apply Hout;
                  unfold GO_MAC, ESTACK, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)
              | (intros _; apply (apresent_writable SEGS); apply HJpres2; unfold GB_STK; lia)
              | lia ]. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E 45 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
    assert (HEIa : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLD1 : forall q, (q < 45)%nat -> ew E1 q = ew E q)
      by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
    clear HE1.
    assert (F2' : ew E1 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F2). clear F2. rename F2' into F2.
    assert (F3' : ew E1 3 = Z_to_bv 64 (as_gp B)) by (rewrite OLD1 by lia; exact F3). clear F3. rename F3' into F3.
    assert (F4' : ew E1 4 = Z_to_bv 64 (as_tp B)) by (rewrite OLD1 by lia; exact F4). clear F4. rename F4' into F4.
    assert (F8' : ew E1 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact F8). clear F8. rename F8' into F8.
    assert (F9' : ew E1 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F9). clear F9. rename F9' into F9.
    assert (F18' : ew E1 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD1 by lia; exact F18). clear F18. rename F18' into F18.
    assert (F20' : ew E1 20 = Z_to_bv 64 r) by (rewrite OLD1 by lia; exact F20). clear F20. rename F20' into F20.
    assert (F24' : ew E1 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite OLD1 by lia; exact F24). clear F24. rename F24' into F24.
    assert (F25' : ew E1 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite OLD1 by lia; exact F25). clear F25. rename F25' into F25.
    assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite OLD1 by lia; exact F32). clear F32. rename F32' into F32.
    assert (F33' : ew E1 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite OLD1 by lia; exact F33). clear F33. rename F33' into F33.
    assert (F36' : ew E1 36 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (r + 280))) by (rewrite OLD1 by lia; exact F36).
    clear F36. rename F36' into F36.
    assert (F38' : ew E1 38 = Z_to_bv 64 (gF cx fp)) by (rewrite OLD1 by lia; exact F38). clear F38. rename F38' into F38.
    assert (FB' : forall j, (j < 6)%nat -> ew E1 (39 + j) = w64 (nth j (c2h_bytes cx pos) 0))
      by (intros j Hj; rewrite OLD1 by lia; exact (FB j Hj)). clear FB. rename FB' into FB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
    pose proof (st_ok_pi_add_region E1 _ _ (c2_frame c2_mac5 37 38) HS eq_refl
      (c2_frameA_ok cx fp E1 W3 mem2 ly3 S3 md2 (proj1 HJ2) Hfin EF F38 HF0 ltac:(lia) HM5)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, c2_frame; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
            rewrite ?F38, ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
            repeat split; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)) as HS1.
    clear HS. rename HS1 into HS.
    assert (SHOK1 : sh_ok SEGS c2_Bx (c2h_SH 0) E1 (mrestrict (w_H W3) mem2)).
    { apply (c2h_sh_gen cx fp pos 0 E1 W3 mem2 F18 F38 F32).
      + lia.
      + destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia.
      + pose proof (gb_mac_ra B MT LAWS cx fp W3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) ly3 S3 md2 k HB HJ2 HFR 0 6
          (c2_hk_gshadow cx fp W3 r ms3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) HKA HSHF HSHh HSH) ltac:(lia) ltac:(lia)) as Hra.
        replace (gF cx fp + GO_MAC + 0) with (gF cx fp + 32) in Hra by (unfold GO_MAC; lia). exact Hra.
      + exact HFapp.
      + intros Hk0. exfalso. exact (Hk0 eq_refl). }
    clear SHOK HJ. rename SHOK1 into SHOK. rename HJ2 into HJ.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr2 F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    psrr_branch_tok RUN BR HS SHOK c2_span.
    2: { exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite F33, unsigned_lit_small in Hc by lia.
         match type of Hc with context [Z_to_bv 64 (c_n cx - pos + ?x)] => replace (c_n cx - pos + x) with 0 in Hc by lia end.
         vm_compute in Hc. discriminate. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr2 F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 0 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 0) bs ms3 msF md3 _ [0; 64; 171; 0; 0; nth 0 (c2h_bytes cx pos) 0]
      HK HB HFR HBLK HINV HMO Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * reflexivity.
    * constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|].
      constructor; [apply c2h_bytes_nth_rng | constructor].
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 0%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ (cbn [sv_denot]; reflexivity)
                | (apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB 0%nat ltac:(lia)) | apply c2_valsA_rng])
                | (cbn [sv_denot]; rewrite (c2h_bytes_out cx pos 0) by lia; reflexivity) ]
        | apply c2_valsA_rng ]).
- (* kk = 1 *)
  paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
  c2h_keep HKA F9 F38 HGB.
  psrr_branch_tok RUN BR HS SHOK c2_span.
  + (* op & 4 <> 0: the six-byte loop *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    psrr_branch_tok RUN BR HS SHOK c2_span.
    2: { exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite F33, unsigned_lit_small in Hc by lia.
         match type of Hc with context [Z_to_bv 64 (c_n cx - pos + ?x)] => replace (c_n cx - pos + x) with 0 in Hc by lia end.
         vm_compute in Hc. discriminate. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 1 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 1) bs ms3 msF md3 _ (c2h_bytes cx pos) HK HB HFR HBLK HINV HMO
      Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * exact Hbl.
    * apply c2h_bytes_rng.
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      lazymatch goal with |- aview _ _ _ (_ + (32 + ?jz)) = _ =>
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 1%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB (Z.to_nat jz) ltac:(lia)) | apply c2h_bytes_nth_rng]
                | cbn [sv_denot]; rewrite (c2h_bytes_out cx pos (Z.to_nat jz)) by lia; reflexivity ]
        | apply c2h_bytes_nth_rng ]) end.
  + (* op & 4 = 0: memcpy (read_mac.base, 5 bytes), then one input byte *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msT end.
    pose proof (c2_hk_gshadow cx fp W3 r ms3 msT HKA HSHF HSHh HSH) as HSHT.
    pmkst HS.
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
    pose proof HJ as (HART & _).
    pose proof (c2_rom B MT cx W3 HB (VAL (A_OBJ 4)) [0; 64; 171; 0; 0] _ _ _ _ _ _ HRMB HJ) as HRT.
    destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem msT) _ (VAL (A_OBJ 4)) 5 (VAL (A_OBJ 4)) 5
      HGLOB ltac:(unfold BX_G; right; right; left; reflexivity) HISV HART ltac:(lia) ltac:(lia) ltac:(lia) HM1 HM2)
      as [HXra HXhv].
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
    eapply SRr_bind;
    [ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA BS___asan_memcpy) AMEMCPY W3 rg mm
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (gF cx fp + GO_MAC) (VAL (A_OBJ 4)) 5 (c_sp1 cx - spZ (c_regs cx)) _ HJ);
      [ rewrite Ra0, F38, unsigned_lit_small by lia; reflexivity
      | rewrite Ra1; change 245%nat with (A_OBJ 4); apply (img_env_atomP E (A_OBJ 4) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia
      | rewrite Ra2; reflexivity
      | lia | unfold GO_MAC; lia | unfold GO_MAC; lia
      | unfold spZ at 1; rewrite Rsp, F2, unsigned_lit_small by lia; lia
      | exact Ho16
      | lia
      | unfold ESTACK, GB_STK; lia
      | rewrite Rgp, F3; reflexivity
      | rewrite Rtp, F4; reflexivity
      | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; right; right; exists GB_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; rewrite EF;
          change (fs_frame_bytes GB_CID) with 512; cbn [fst snd]; unfold GO_MAC in *; lia
        | unfold ESTACK, GO_MAC in *; lia ]
      | unfold amem_range; unfold in_app in HFia; unfold GO_MAC, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *; lia
      | pose proof (gb_mac_ra B MT LAWS cx fp W3 msT ly3 S3 _ k HB HJ HFR 0 5 HSHT ltac:(lia) ltac:(lia)) as Hra;
        rewrite Z.add_0_r in Hra; exact Hra
      | intros _; apply (shadow_hull_vis_of_frame _ _ LAWS _ _ _ _ _ GB_CID fp _ _ HART ltac:(rewrite HFR; left; reflexivity));
        try rewrite EF; change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia;
            rewrite (HRT (a - VAL (A_OBJ 4)) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)); discriminate
          | unfold spZ at 1 2; rewrite Rsp, F2, unsigned_lit_small by lia; unfold ESTACK; lia ] |];
        split; [ exact (c2_frame_rom_disj ly3 S3 W3 _ _ cx fp _ _ HART Hfin EF HRMB (gF cx fp + GO_MAC) 5
                   ltac:(unfold GO_MAC; lia) ltac:(unfold GO_MAC; lia) ltac:(lia) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)) |];
        split; [ unfold amem_range, kLowMemEnd; lia |];
        split; [ exact HXra | intros _; exact HXhv ] ]
    | ] end.
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout & Hpres2).
    assert (HKA2 : c2_hkeep cx fp W3 r (ms_mem ms3) mem2).
    { apply (c2_hk_trans cx fp W3 r _ (ms_mem msT) mem2 HKA HKA).
      apply (c2_hk_call cx fp W3 r (ms_mem msT) mem2 (gF cx fp + GO_MAC) 5); [lia | lia | | exact HGB2].
      intros a Ha H1 H2. apply Hout; [exact Ha | exact H1 | lia]. }
    clear HKA. rename HKA2 into HKA.
    assert (HM5 : forall j, 0 <= j < 5 -> aview SEGS (w_H W3) mem2 (gF cx fp + GO_MAC + j) =
      Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0)).
    { intros j Hj. rewrite (Heff j Hj). exact (HRT j ltac:(cbn; lia)). }
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
    jafter_call_keep_pi HS 45%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 2; 3; 4]%nat HS2.
    match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val];
        rewrite ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
        intros a Ha;
        first [ (apply (mbyte_of_aview SEGS); apply Hout;
                  unfold GO_MAC, ESTACK, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)
              | (intros _; apply (apresent_writable SEGS); apply HJpres2; unfold GB_STK; lia)
              | lia ]. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E 45 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
    assert (HEIa : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLD1 : forall q, (q < 45)%nat -> ew E1 q = ew E q)
      by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
    clear HE1.
    assert (F2' : ew E1 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F2). clear F2. rename F2' into F2.
    assert (F3' : ew E1 3 = Z_to_bv 64 (as_gp B)) by (rewrite OLD1 by lia; exact F3). clear F3. rename F3' into F3.
    assert (F4' : ew E1 4 = Z_to_bv 64 (as_tp B)) by (rewrite OLD1 by lia; exact F4). clear F4. rename F4' into F4.
    assert (F8' : ew E1 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact F8). clear F8. rename F8' into F8.
    assert (F9' : ew E1 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F9). clear F9. rename F9' into F9.
    assert (F18' : ew E1 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD1 by lia; exact F18). clear F18. rename F18' into F18.
    assert (F20' : ew E1 20 = Z_to_bv 64 r) by (rewrite OLD1 by lia; exact F20). clear F20. rename F20' into F20.
    assert (F24' : ew E1 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite OLD1 by lia; exact F24). clear F24. rename F24' into F24.
    assert (F25' : ew E1 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite OLD1 by lia; exact F25). clear F25. rename F25' into F25.
    assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite OLD1 by lia; exact F32). clear F32. rename F32' into F32.
    assert (F33' : ew E1 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite OLD1 by lia; exact F33). clear F33. rename F33' into F33.
    assert (F36' : ew E1 36 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (r + 280))) by (rewrite OLD1 by lia; exact F36).
    clear F36. rename F36' into F36.
    assert (F38' : ew E1 38 = Z_to_bv 64 (gF cx fp)) by (rewrite OLD1 by lia; exact F38). clear F38. rename F38' into F38.
    assert (FB' : forall j, (j < 6)%nat -> ew E1 (39 + j) = w64 (nth j (c2h_bytes cx pos) 0))
      by (intros j Hj; rewrite OLD1 by lia; exact (FB j Hj)). clear FB. rename FB' into FB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
    pose proof (st_ok_pi_add_region E1 _ _ (c2_frame c2_mac5 37 38) HS eq_refl
      (c2_frameA_ok cx fp E1 W3 mem2 ly3 S3 md2 (proj1 HJ2) Hfin EF F38 HF0 ltac:(lia) HM5)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, c2_frame; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
            rewrite ?F38, ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
            repeat split; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)) as HS1.
    clear HS. rename HS1 into HS.
    assert (SHOK1 : sh_ok SEGS c2_Bx (c2h_SH 1) E1 (mrestrict (w_H W3) mem2)).
    { apply (c2h_sh_gen cx fp pos 1 E1 W3 mem2 F18 F38 F32).
      + lia.
      + destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia.
      + pose proof (gb_mac_ra B MT LAWS cx fp W3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) ly3 S3 md2 k HB HJ2 HFR 0 6
          (c2_hk_gshadow cx fp W3 r ms3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) HKA HSHF HSHh HSH) ltac:(lia) ltac:(lia)) as Hra.
        replace (gF cx fp + GO_MAC + 0) with (gF cx fp + 32) in Hra by (unfold GO_MAC; lia). exact Hra.
      + exact HFapp.
      + intros _. destruct Hinp as [(Hn0 & _) | (_ & Hin3 & Hp4 & Hpce & Hpia & _)]; [lia|].
        split.
        * pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
          apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hin3); lia.
        * unfold in_app in Hpia. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
    clear SHOK HJ. rename SHOK1 into SHOK. rename HJ2 into HJ.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr2 F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 1 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 1) bs ms3 msF md3 _ [0; 64; 171; 0; 0; nth 0 (c2h_bytes cx pos) 0]
      HK HB HFR HBLK HINV HMO Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * reflexivity.
    * constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|].
      constructor; [apply c2h_bytes_nth_rng | constructor].
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 0%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ (cbn [sv_denot]; reflexivity)
                | (apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB 0%nat ltac:(lia)) | apply c2_valsA_rng])
                | (cbn [sv_denot]; rewrite (c2h_bytes_out cx pos 0) by lia; reflexivity) ]
        | apply c2_valsA_rng ]).
- (* kk = 2 *)
  paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
  c2h_keep HKA F9 F38 HGB.
  psrr_branch_tok RUN BR HS SHOK c2_span.
  + (* op & 4 <> 0: the six-byte loop *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    psrr_branch_tok RUN BR HS SHOK c2_span.
    2: { exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite F33, unsigned_lit_small in Hc by lia.
         match type of Hc with context [Z_to_bv 64 (c_n cx - pos + ?x)] => replace (c_n cx - pos + x) with 0 in Hc by lia end.
         vm_compute in Hc. discriminate. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 2 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 2) bs ms3 msF md3 _ (c2h_bytes cx pos) HK HB HFR HBLK HINV HMO
      Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * exact Hbl.
    * apply c2h_bytes_rng.
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      lazymatch goal with |- aview _ _ _ (_ + (32 + ?jz)) = _ =>
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 1%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB (Z.to_nat jz) ltac:(lia)) | apply c2h_bytes_nth_rng]
                | cbn [sv_denot]; rewrite (c2h_bytes_out cx pos (Z.to_nat jz)) by lia; reflexivity ]
        | apply c2h_bytes_nth_rng ]) end.
  + (* op & 4 = 0: memcpy (read_mac.base, 5 bytes), then one input byte *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msT end.
    pose proof (c2_hk_gshadow cx fp W3 r ms3 msT HKA HSHF HSHh HSH) as HSHT.
    pmkst HS.
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
    pose proof HJ as (HART & _).
    pose proof (c2_rom B MT cx W3 HB (VAL (A_OBJ 4)) [0; 64; 171; 0; 0] _ _ _ _ _ _ HRMB HJ) as HRT.
    destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem msT) _ (VAL (A_OBJ 4)) 5 (VAL (A_OBJ 4)) 5
      HGLOB ltac:(unfold BX_G; right; right; left; reflexivity) HISV HART ltac:(lia) ltac:(lia) ltac:(lia) HM1 HM2)
      as [HXra HXhv].
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
    eapply SRr_bind;
    [ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA BS___asan_memcpy) AMEMCPY W3 rg mm
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (gF cx fp + GO_MAC) (VAL (A_OBJ 4)) 5 (c_sp1 cx - spZ (c_regs cx)) _ HJ);
      [ rewrite Ra0, F38, unsigned_lit_small by lia; reflexivity
      | rewrite Ra1; change 245%nat with (A_OBJ 4); apply (img_env_atomP E (A_OBJ 4) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia
      | rewrite Ra2; reflexivity
      | lia | unfold GO_MAC; lia | unfold GO_MAC; lia
      | unfold spZ at 1; rewrite Rsp, F2, unsigned_lit_small by lia; lia
      | exact Ho16
      | lia
      | unfold ESTACK, GB_STK; lia
      | rewrite Rgp, F3; reflexivity
      | rewrite Rtp, F4; reflexivity
      | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; right; right; exists GB_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; rewrite EF;
          change (fs_frame_bytes GB_CID) with 512; cbn [fst snd]; unfold GO_MAC in *; lia
        | unfold ESTACK, GO_MAC in *; lia ]
      | unfold amem_range; unfold in_app in HFia; unfold GO_MAC, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *; lia
      | pose proof (gb_mac_ra B MT LAWS cx fp W3 msT ly3 S3 _ k HB HJ HFR 0 5 HSHT ltac:(lia) ltac:(lia)) as Hra;
        rewrite Z.add_0_r in Hra; exact Hra
      | intros _; apply (shadow_hull_vis_of_frame _ _ LAWS _ _ _ _ _ GB_CID fp _ _ HART ltac:(rewrite HFR; left; reflexivity));
        try rewrite EF; change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia;
            rewrite (HRT (a - VAL (A_OBJ 4)) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)); discriminate
          | unfold spZ at 1 2; rewrite Rsp, F2, unsigned_lit_small by lia; unfold ESTACK; lia ] |];
        split; [ exact (c2_frame_rom_disj ly3 S3 W3 _ _ cx fp _ _ HART Hfin EF HRMB (gF cx fp + GO_MAC) 5
                   ltac:(unfold GO_MAC; lia) ltac:(unfold GO_MAC; lia) ltac:(lia) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)) |];
        split; [ unfold amem_range, kLowMemEnd; lia |];
        split; [ exact HXra | intros _; exact HXhv ] ]
    | ] end.
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout & Hpres2).
    assert (HKA2 : c2_hkeep cx fp W3 r (ms_mem ms3) mem2).
    { apply (c2_hk_trans cx fp W3 r _ (ms_mem msT) mem2 HKA HKA).
      apply (c2_hk_call cx fp W3 r (ms_mem msT) mem2 (gF cx fp + GO_MAC) 5); [lia | lia | | exact HGB2].
      intros a Ha H1 H2. apply Hout; [exact Ha | exact H1 | lia]. }
    clear HKA. rename HKA2 into HKA.
    assert (HM5 : forall j, 0 <= j < 5 -> aview SEGS (w_H W3) mem2 (gF cx fp + GO_MAC + j) =
      Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0)).
    { intros j Hj. rewrite (Heff j Hj). exact (HRT j ltac:(cbn; lia)). }
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
    jafter_call_keep_pi HS 45%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 2; 3; 4]%nat HS2.
    match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val];
        rewrite ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
        intros a Ha;
        first [ (apply (mbyte_of_aview SEGS); apply Hout;
                  unfold GO_MAC, ESTACK, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)
              | (intros _; apply (apresent_writable SEGS); apply HJpres2; unfold GB_STK; lia)
              | lia ]. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E 45 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
    assert (HEIa : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLD1 : forall q, (q < 45)%nat -> ew E1 q = ew E q)
      by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
    clear HE1.
    assert (F2' : ew E1 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F2). clear F2. rename F2' into F2.
    assert (F3' : ew E1 3 = Z_to_bv 64 (as_gp B)) by (rewrite OLD1 by lia; exact F3). clear F3. rename F3' into F3.
    assert (F4' : ew E1 4 = Z_to_bv 64 (as_tp B)) by (rewrite OLD1 by lia; exact F4). clear F4. rename F4' into F4.
    assert (F8' : ew E1 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact F8). clear F8. rename F8' into F8.
    assert (F9' : ew E1 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F9). clear F9. rename F9' into F9.
    assert (F18' : ew E1 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD1 by lia; exact F18). clear F18. rename F18' into F18.
    assert (F20' : ew E1 20 = Z_to_bv 64 r) by (rewrite OLD1 by lia; exact F20). clear F20. rename F20' into F20.
    assert (F24' : ew E1 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite OLD1 by lia; exact F24). clear F24. rename F24' into F24.
    assert (F25' : ew E1 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite OLD1 by lia; exact F25). clear F25. rename F25' into F25.
    assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite OLD1 by lia; exact F32). clear F32. rename F32' into F32.
    assert (F33' : ew E1 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite OLD1 by lia; exact F33). clear F33. rename F33' into F33.
    assert (F36' : ew E1 36 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (r + 280))) by (rewrite OLD1 by lia; exact F36).
    clear F36. rename F36' into F36.
    assert (F38' : ew E1 38 = Z_to_bv 64 (gF cx fp)) by (rewrite OLD1 by lia; exact F38). clear F38. rename F38' into F38.
    assert (FB' : forall j, (j < 6)%nat -> ew E1 (39 + j) = w64 (nth j (c2h_bytes cx pos) 0))
      by (intros j Hj; rewrite OLD1 by lia; exact (FB j Hj)). clear FB. rename FB' into FB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
    pose proof (st_ok_pi_add_region E1 _ _ (c2_frame c2_mac5 37 38) HS eq_refl
      (c2_frameA_ok cx fp E1 W3 mem2 ly3 S3 md2 (proj1 HJ2) Hfin EF F38 HF0 ltac:(lia) HM5)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, c2_frame; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
            rewrite ?F38, ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
            repeat split; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)) as HS1.
    clear HS. rename HS1 into HS.
    assert (SHOK1 : sh_ok SEGS c2_Bx (c2h_SH 2) E1 (mrestrict (w_H W3) mem2)).
    { apply (c2h_sh_gen cx fp pos 2 E1 W3 mem2 F18 F38 F32).
      + lia.
      + destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia.
      + pose proof (gb_mac_ra B MT LAWS cx fp W3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) ly3 S3 md2 k HB HJ2 HFR 0 6
          (c2_hk_gshadow cx fp W3 r ms3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) HKA HSHF HSHh HSH) ltac:(lia) ltac:(lia)) as Hra.
        replace (gF cx fp + GO_MAC + 0) with (gF cx fp + 32) in Hra by (unfold GO_MAC; lia). exact Hra.
      + exact HFapp.
      + intros _. destruct Hinp as [(Hn0 & _) | (_ & Hin3 & Hp4 & Hpce & Hpia & _)]; [lia|].
        split.
        * pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
          apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hin3); lia.
        * unfold in_app in Hpia. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
    clear SHOK HJ. rename SHOK1 into SHOK. rename HJ2 into HJ.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr2 F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 1 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 1) bs ms3 msF md3 _ [0; 64; 171; 0; 0; nth 0 (c2h_bytes cx pos) 0]
      HK HB HFR HBLK HINV HMO Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * reflexivity.
    * constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|].
      constructor; [apply c2h_bytes_nth_rng | constructor].
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 0%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ (cbn [sv_denot]; reflexivity)
                | (apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB 0%nat ltac:(lia)) | apply c2_valsA_rng])
                | (cbn [sv_denot]; rewrite (c2h_bytes_out cx pos 0) by lia; reflexivity) ]
        | apply c2_valsA_rng ]).
- (* kk = 3 *)
  paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
  c2h_keep HKA F9 F38 HGB.
  psrr_branch_tok RUN BR HS SHOK c2_span.
  + (* op & 4 <> 0: the six-byte loop *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    psrr_branch_tok RUN BR HS SHOK c2_span.
    2: { exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite F33, unsigned_lit_small in Hc by lia.
         match type of Hc with context [Z_to_bv 64 (c_n cx - pos + ?x)] => replace (c_n cx - pos + x) with 0 in Hc by lia end.
         vm_compute in Hc. discriminate. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 3 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 3) bs ms3 msF md3 _ (c2h_bytes cx pos) HK HB HFR HBLK HINV HMO
      Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * exact Hbl.
    * apply c2h_bytes_rng.
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      lazymatch goal with |- aview _ _ _ (_ + (32 + ?jz)) = _ =>
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 1%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB (Z.to_nat jz) ltac:(lia)) | apply c2h_bytes_nth_rng]
                | cbn [sv_denot]; rewrite (c2h_bytes_out cx pos (Z.to_nat jz)) by lia; reflexivity ]
        | apply c2h_bytes_nth_rng ]) end.
  + (* op & 4 = 0: memcpy (read_mac.base, 5 bytes), then one input byte *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msT end.
    pose proof (c2_hk_gshadow cx fp W3 r ms3 msT HKA HSHF HSHh HSH) as HSHT.
    pmkst HS.
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
    pose proof HJ as (HART & _).
    pose proof (c2_rom B MT cx W3 HB (VAL (A_OBJ 4)) [0; 64; 171; 0; 0] _ _ _ _ _ _ HRMB HJ) as HRT.
    destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem msT) _ (VAL (A_OBJ 4)) 5 (VAL (A_OBJ 4)) 5
      HGLOB ltac:(unfold BX_G; right; right; left; reflexivity) HISV HART ltac:(lia) ltac:(lia) ltac:(lia) HM1 HM2)
      as [HXra HXhv].
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
    eapply SRr_bind;
    [ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA BS___asan_memcpy) AMEMCPY W3 rg mm
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (gF cx fp + GO_MAC) (VAL (A_OBJ 4)) 5 (c_sp1 cx - spZ (c_regs cx)) _ HJ);
      [ rewrite Ra0, F38, unsigned_lit_small by lia; reflexivity
      | rewrite Ra1; change 245%nat with (A_OBJ 4); apply (img_env_atomP E (A_OBJ 4) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia
      | rewrite Ra2; reflexivity
      | lia | unfold GO_MAC; lia | unfold GO_MAC; lia
      | unfold spZ at 1; rewrite Rsp, F2, unsigned_lit_small by lia; lia
      | exact Ho16
      | lia
      | unfold ESTACK, GB_STK; lia
      | rewrite Rgp, F3; reflexivity
      | rewrite Rtp, F4; reflexivity
      | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; right; right; exists GB_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; rewrite EF;
          change (fs_frame_bytes GB_CID) with 512; cbn [fst snd]; unfold GO_MAC in *; lia
        | unfold ESTACK, GO_MAC in *; lia ]
      | unfold amem_range; unfold in_app in HFia; unfold GO_MAC, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *; lia
      | pose proof (gb_mac_ra B MT LAWS cx fp W3 msT ly3 S3 _ k HB HJ HFR 0 5 HSHT ltac:(lia) ltac:(lia)) as Hra;
        rewrite Z.add_0_r in Hra; exact Hra
      | intros _; apply (shadow_hull_vis_of_frame _ _ LAWS _ _ _ _ _ GB_CID fp _ _ HART ltac:(rewrite HFR; left; reflexivity));
        try rewrite EF; change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia;
            rewrite (HRT (a - VAL (A_OBJ 4)) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)); discriminate
          | unfold spZ at 1 2; rewrite Rsp, F2, unsigned_lit_small by lia; unfold ESTACK; lia ] |];
        split; [ exact (c2_frame_rom_disj ly3 S3 W3 _ _ cx fp _ _ HART Hfin EF HRMB (gF cx fp + GO_MAC) 5
                   ltac:(unfold GO_MAC; lia) ltac:(unfold GO_MAC; lia) ltac:(lia) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)) |];
        split; [ unfold amem_range, kLowMemEnd; lia |];
        split; [ exact HXra | intros _; exact HXhv ] ]
    | ] end.
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout & Hpres2).
    assert (HKA2 : c2_hkeep cx fp W3 r (ms_mem ms3) mem2).
    { apply (c2_hk_trans cx fp W3 r _ (ms_mem msT) mem2 HKA HKA).
      apply (c2_hk_call cx fp W3 r (ms_mem msT) mem2 (gF cx fp + GO_MAC) 5); [lia | lia | | exact HGB2].
      intros a Ha H1 H2. apply Hout; [exact Ha | exact H1 | lia]. }
    clear HKA. rename HKA2 into HKA.
    assert (HM5 : forall j, 0 <= j < 5 -> aview SEGS (w_H W3) mem2 (gF cx fp + GO_MAC + j) =
      Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0)).
    { intros j Hj. rewrite (Heff j Hj). exact (HRT j ltac:(cbn; lia)). }
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
    jafter_call_keep_pi HS 45%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 2; 3; 4]%nat HS2.
    match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val];
        rewrite ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
        intros a Ha;
        first [ (apply (mbyte_of_aview SEGS); apply Hout;
                  unfold GO_MAC, ESTACK, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)
              | (intros _; apply (apresent_writable SEGS); apply HJpres2; unfold GB_STK; lia)
              | lia ]. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E 45 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
    assert (HEIa : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLD1 : forall q, (q < 45)%nat -> ew E1 q = ew E q)
      by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
    clear HE1.
    assert (F2' : ew E1 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F2). clear F2. rename F2' into F2.
    assert (F3' : ew E1 3 = Z_to_bv 64 (as_gp B)) by (rewrite OLD1 by lia; exact F3). clear F3. rename F3' into F3.
    assert (F4' : ew E1 4 = Z_to_bv 64 (as_tp B)) by (rewrite OLD1 by lia; exact F4). clear F4. rename F4' into F4.
    assert (F8' : ew E1 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact F8). clear F8. rename F8' into F8.
    assert (F9' : ew E1 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F9). clear F9. rename F9' into F9.
    assert (F18' : ew E1 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD1 by lia; exact F18). clear F18. rename F18' into F18.
    assert (F20' : ew E1 20 = Z_to_bv 64 r) by (rewrite OLD1 by lia; exact F20). clear F20. rename F20' into F20.
    assert (F24' : ew E1 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite OLD1 by lia; exact F24). clear F24. rename F24' into F24.
    assert (F25' : ew E1 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite OLD1 by lia; exact F25). clear F25. rename F25' into F25.
    assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite OLD1 by lia; exact F32). clear F32. rename F32' into F32.
    assert (F33' : ew E1 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite OLD1 by lia; exact F33). clear F33. rename F33' into F33.
    assert (F36' : ew E1 36 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (r + 280))) by (rewrite OLD1 by lia; exact F36).
    clear F36. rename F36' into F36.
    assert (F38' : ew E1 38 = Z_to_bv 64 (gF cx fp)) by (rewrite OLD1 by lia; exact F38). clear F38. rename F38' into F38.
    assert (FB' : forall j, (j < 6)%nat -> ew E1 (39 + j) = w64 (nth j (c2h_bytes cx pos) 0))
      by (intros j Hj; rewrite OLD1 by lia; exact (FB j Hj)). clear FB. rename FB' into FB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
    pose proof (st_ok_pi_add_region E1 _ _ (c2_frame c2_mac5 37 38) HS eq_refl
      (c2_frameA_ok cx fp E1 W3 mem2 ly3 S3 md2 (proj1 HJ2) Hfin EF F38 HF0 ltac:(lia) HM5)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, c2_frame; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
            rewrite ?F38, ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
            repeat split; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)) as HS1.
    clear HS. rename HS1 into HS.
    assert (SHOK1 : sh_ok SEGS c2_Bx (c2h_SH 3) E1 (mrestrict (w_H W3) mem2)).
    { apply (c2h_sh_gen cx fp pos 3 E1 W3 mem2 F18 F38 F32).
      + lia.
      + destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia.
      + pose proof (gb_mac_ra B MT LAWS cx fp W3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) ly3 S3 md2 k HB HJ2 HFR 0 6
          (c2_hk_gshadow cx fp W3 r ms3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) HKA HSHF HSHh HSH) ltac:(lia) ltac:(lia)) as Hra.
        replace (gF cx fp + GO_MAC + 0) with (gF cx fp + 32) in Hra by (unfold GO_MAC; lia). exact Hra.
      + exact HFapp.
      + intros _. destruct Hinp as [(Hn0 & _) | (_ & Hin3 & Hp4 & Hpce & Hpia & _)]; [lia|].
        split.
        * pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
          apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hin3); lia.
        * unfold in_app in Hpia. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
    clear SHOK HJ. rename SHOK1 into SHOK. rename HJ2 into HJ.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr2 F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 1 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 1) bs ms3 msF md3 _ [0; 64; 171; 0; 0; nth 0 (c2h_bytes cx pos) 0]
      HK HB HFR HBLK HINV HMO Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * reflexivity.
    * constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|].
      constructor; [apply c2h_bytes_nth_rng | constructor].
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 0%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ (cbn [sv_denot]; reflexivity)
                | (apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB 0%nat ltac:(lia)) | apply c2_valsA_rng])
                | (cbn [sv_denot]; rewrite (c2h_bytes_out cx pos 0) by lia; reflexivity) ]
        | apply c2_valsA_rng ]).
- (* kk = 4 *)
  paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
  c2h_keep HKA F9 F38 HGB.
  psrr_branch_tok RUN BR HS SHOK c2_span.
  + (* op & 4 <> 0: the six-byte loop *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    psrr_branch_tok RUN BR HS SHOK c2_span.
    2: { exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite F33, unsigned_lit_small in Hc by lia.
         match type of Hc with context [Z_to_bv 64 (c_n cx - pos + ?x)] => replace (c_n cx - pos + x) with 0 in Hc by lia end.
         vm_compute in Hc. discriminate. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 4 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 4) bs ms3 msF md3 _ (c2h_bytes cx pos) HK HB HFR HBLK HINV HMO
      Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * exact Hbl.
    * apply c2h_bytes_rng.
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      lazymatch goal with |- aview _ _ _ (_ + (32 + ?jz)) = _ =>
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 1%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB (Z.to_nat jz) ltac:(lia)) | apply c2h_bytes_nth_rng]
                | cbn [sv_denot]; rewrite (c2h_bytes_out cx pos (Z.to_nat jz)) by lia; reflexivity ]
        | apply c2h_bytes_nth_rng ]) end.
  + (* op & 4 = 0: memcpy (read_mac.base, 5 bytes), then one input byte *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msT end.
    pose proof (c2_hk_gshadow cx fp W3 r ms3 msT HKA HSHF HSHh HSH) as HSHT.
    pmkst HS.
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
    pose proof HJ as (HART & _).
    pose proof (c2_rom B MT cx W3 HB (VAL (A_OBJ 4)) [0; 64; 171; 0; 0] _ _ _ _ _ _ HRMB HJ) as HRT.
    destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem msT) _ (VAL (A_OBJ 4)) 5 (VAL (A_OBJ 4)) 5
      HGLOB ltac:(unfold BX_G; right; right; left; reflexivity) HISV HART ltac:(lia) ltac:(lia) ltac:(lia) HM1 HM2)
      as [HXra HXhv].
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
    eapply SRr_bind;
    [ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA BS___asan_memcpy) AMEMCPY W3 rg mm
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (gF cx fp + GO_MAC) (VAL (A_OBJ 4)) 5 (c_sp1 cx - spZ (c_regs cx)) _ HJ);
      [ rewrite Ra0, F38, unsigned_lit_small by lia; reflexivity
      | rewrite Ra1; change 245%nat with (A_OBJ 4); apply (img_env_atomP E (A_OBJ 4) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia
      | rewrite Ra2; reflexivity
      | lia | unfold GO_MAC; lia | unfold GO_MAC; lia
      | unfold spZ at 1; rewrite Rsp, F2, unsigned_lit_small by lia; lia
      | exact Ho16
      | lia
      | unfold ESTACK, GB_STK; lia
      | rewrite Rgp, F3; reflexivity
      | rewrite Rtp, F4; reflexivity
      | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; right; right; exists GB_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; rewrite EF;
          change (fs_frame_bytes GB_CID) with 512; cbn [fst snd]; unfold GO_MAC in *; lia
        | unfold ESTACK, GO_MAC in *; lia ]
      | unfold amem_range; unfold in_app in HFia; unfold GO_MAC, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *; lia
      | pose proof (gb_mac_ra B MT LAWS cx fp W3 msT ly3 S3 _ k HB HJ HFR 0 5 HSHT ltac:(lia) ltac:(lia)) as Hra;
        rewrite Z.add_0_r in Hra; exact Hra
      | intros _; apply (shadow_hull_vis_of_frame _ _ LAWS _ _ _ _ _ GB_CID fp _ _ HART ltac:(rewrite HFR; left; reflexivity));
        try rewrite EF; change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia;
            rewrite (HRT (a - VAL (A_OBJ 4)) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)); discriminate
          | unfold spZ at 1 2; rewrite Rsp, F2, unsigned_lit_small by lia; unfold ESTACK; lia ] |];
        split; [ exact (c2_frame_rom_disj ly3 S3 W3 _ _ cx fp _ _ HART Hfin EF HRMB (gF cx fp + GO_MAC) 5
                   ltac:(unfold GO_MAC; lia) ltac:(unfold GO_MAC; lia) ltac:(lia) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)) |];
        split; [ unfold amem_range, kLowMemEnd; lia |];
        split; [ exact HXra | intros _; exact HXhv ] ]
    | ] end.
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout & Hpres2).
    assert (HKA2 : c2_hkeep cx fp W3 r (ms_mem ms3) mem2).
    { apply (c2_hk_trans cx fp W3 r _ (ms_mem msT) mem2 HKA HKA).
      apply (c2_hk_call cx fp W3 r (ms_mem msT) mem2 (gF cx fp + GO_MAC) 5); [lia | lia | | exact HGB2].
      intros a Ha H1 H2. apply Hout; [exact Ha | exact H1 | lia]. }
    clear HKA. rename HKA2 into HKA.
    assert (HM5 : forall j, 0 <= j < 5 -> aview SEGS (w_H W3) mem2 (gF cx fp + GO_MAC + j) =
      Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0)).
    { intros j Hj. rewrite (Heff j Hj). exact (HRT j ltac:(cbn; lia)). }
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
    jafter_call_keep_pi HS 45%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 2; 3; 4]%nat HS2.
    match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val];
        rewrite ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
        intros a Ha;
        first [ (apply (mbyte_of_aview SEGS); apply Hout;
                  unfold GO_MAC, ESTACK, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)
              | (intros _; apply (apresent_writable SEGS); apply HJpres2; unfold GB_STK; lia)
              | lia ]. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E 45 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
    assert (HEIa : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLD1 : forall q, (q < 45)%nat -> ew E1 q = ew E q)
      by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
    clear HE1.
    assert (F2' : ew E1 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F2). clear F2. rename F2' into F2.
    assert (F3' : ew E1 3 = Z_to_bv 64 (as_gp B)) by (rewrite OLD1 by lia; exact F3). clear F3. rename F3' into F3.
    assert (F4' : ew E1 4 = Z_to_bv 64 (as_tp B)) by (rewrite OLD1 by lia; exact F4). clear F4. rename F4' into F4.
    assert (F8' : ew E1 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact F8). clear F8. rename F8' into F8.
    assert (F9' : ew E1 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F9). clear F9. rename F9' into F9.
    assert (F18' : ew E1 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD1 by lia; exact F18). clear F18. rename F18' into F18.
    assert (F20' : ew E1 20 = Z_to_bv 64 r) by (rewrite OLD1 by lia; exact F20). clear F20. rename F20' into F20.
    assert (F24' : ew E1 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite OLD1 by lia; exact F24). clear F24. rename F24' into F24.
    assert (F25' : ew E1 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite OLD1 by lia; exact F25). clear F25. rename F25' into F25.
    assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite OLD1 by lia; exact F32). clear F32. rename F32' into F32.
    assert (F33' : ew E1 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite OLD1 by lia; exact F33). clear F33. rename F33' into F33.
    assert (F36' : ew E1 36 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (r + 280))) by (rewrite OLD1 by lia; exact F36).
    clear F36. rename F36' into F36.
    assert (F38' : ew E1 38 = Z_to_bv 64 (gF cx fp)) by (rewrite OLD1 by lia; exact F38). clear F38. rename F38' into F38.
    assert (FB' : forall j, (j < 6)%nat -> ew E1 (39 + j) = w64 (nth j (c2h_bytes cx pos) 0))
      by (intros j Hj; rewrite OLD1 by lia; exact (FB j Hj)). clear FB. rename FB' into FB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
    pose proof (st_ok_pi_add_region E1 _ _ (c2_frame c2_mac5 37 38) HS eq_refl
      (c2_frameA_ok cx fp E1 W3 mem2 ly3 S3 md2 (proj1 HJ2) Hfin EF F38 HF0 ltac:(lia) HM5)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, c2_frame; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
            rewrite ?F38, ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
            repeat split; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)) as HS1.
    clear HS. rename HS1 into HS.
    assert (SHOK1 : sh_ok SEGS c2_Bx (c2h_SH 4) E1 (mrestrict (w_H W3) mem2)).
    { apply (c2h_sh_gen cx fp pos 4 E1 W3 mem2 F18 F38 F32).
      + lia.
      + destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia.
      + pose proof (gb_mac_ra B MT LAWS cx fp W3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) ly3 S3 md2 k HB HJ2 HFR 0 6
          (c2_hk_gshadow cx fp W3 r ms3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) HKA HSHF HSHh HSH) ltac:(lia) ltac:(lia)) as Hra.
        replace (gF cx fp + GO_MAC + 0) with (gF cx fp + 32) in Hra by (unfold GO_MAC; lia). exact Hra.
      + exact HFapp.
      + intros _. destruct Hinp as [(Hn0 & _) | (_ & Hin3 & Hp4 & Hpce & Hpia & _)]; [lia|].
        split.
        * pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
          apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hin3); lia.
        * unfold in_app in Hpia. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
    clear SHOK HJ. rename SHOK1 into SHOK. rename HJ2 into HJ.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr2 F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 1 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 1) bs ms3 msF md3 _ [0; 64; 171; 0; 0; nth 0 (c2h_bytes cx pos) 0]
      HK HB HFR HBLK HINV HMO Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * reflexivity.
    * constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|].
      constructor; [apply c2h_bytes_nth_rng | constructor].
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 0%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ (cbn [sv_denot]; reflexivity)
                | (apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB 0%nat ltac:(lia)) | apply c2_valsA_rng])
                | (cbn [sv_denot]; rewrite (c2h_bytes_out cx pos 0) by lia; reflexivity) ]
        | apply c2_valsA_rng ]).
- (* kk = 5 *)
  paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
  c2h_keep HKA F9 F38 HGB.
  psrr_branch_tok RUN BR HS SHOK c2_span.
  + (* op & 4 <> 0: the six-byte loop *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    psrr_branch_tok RUN BR HS SHOK c2_span.
    2: { exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite F33, unsigned_lit_small in Hc by lia.
         match type of Hc with context [Z_to_bv 64 (c_n cx - pos + ?x)] => replace (c_n cx - pos + x) with 0 in Hc by lia end.
         vm_compute in Hc. discriminate. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 5 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 5) bs ms3 msF md3 _ (c2h_bytes cx pos) HK HB HFR HBLK HINV HMO
      Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * exact Hbl.
    * apply c2h_bytes_rng.
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      lazymatch goal with |- aview _ _ _ (_ + (32 + ?jz)) = _ =>
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 1%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB (Z.to_nat jz) ltac:(lia)) | apply c2h_bytes_nth_rng]
                | cbn [sv_denot]; rewrite (c2h_bytes_out cx pos (Z.to_nat jz)) by lia; reflexivity ]
        | apply c2h_bytes_nth_rng ]) end.
  + (* op & 4 = 0: memcpy (read_mac.base, 5 bytes), then one input byte *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msT end.
    pose proof (c2_hk_gshadow cx fp W3 r ms3 msT HKA HSHF HSHh HSH) as HSHT.
    pmkst HS.
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
    pose proof HJ as (HART & _).
    pose proof (c2_rom B MT cx W3 HB (VAL (A_OBJ 4)) [0; 64; 171; 0; 0] _ _ _ _ _ _ HRMB HJ) as HRT.
    destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem msT) _ (VAL (A_OBJ 4)) 5 (VAL (A_OBJ 4)) 5
      HGLOB ltac:(unfold BX_G; right; right; left; reflexivity) HISV HART ltac:(lia) ltac:(lia) ltac:(lia) HM1 HM2)
      as [HXra HXhv].
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
    eapply SRr_bind;
    [ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA BS___asan_memcpy) AMEMCPY W3 rg mm
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (gF cx fp + GO_MAC) (VAL (A_OBJ 4)) 5 (c_sp1 cx - spZ (c_regs cx)) _ HJ);
      [ rewrite Ra0, F38, unsigned_lit_small by lia; reflexivity
      | rewrite Ra1; change 245%nat with (A_OBJ 4); apply (img_env_atomP E (A_OBJ 4) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia
      | rewrite Ra2; reflexivity
      | lia | unfold GO_MAC; lia | unfold GO_MAC; lia
      | unfold spZ at 1; rewrite Rsp, F2, unsigned_lit_small by lia; lia
      | exact Ho16
      | lia
      | unfold ESTACK, GB_STK; lia
      | rewrite Rgp, F3; reflexivity
      | rewrite Rtp, F4; reflexivity
      | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; right; right; exists GB_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; rewrite EF;
          change (fs_frame_bytes GB_CID) with 512; cbn [fst snd]; unfold GO_MAC in *; lia
        | unfold ESTACK, GO_MAC in *; lia ]
      | unfold amem_range; unfold in_app in HFia; unfold GO_MAC, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *; lia
      | pose proof (gb_mac_ra B MT LAWS cx fp W3 msT ly3 S3 _ k HB HJ HFR 0 5 HSHT ltac:(lia) ltac:(lia)) as Hra;
        rewrite Z.add_0_r in Hra; exact Hra
      | intros _; apply (shadow_hull_vis_of_frame _ _ LAWS _ _ _ _ _ GB_CID fp _ _ HART ltac:(rewrite HFR; left; reflexivity));
        try rewrite EF; change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia;
            rewrite (HRT (a - VAL (A_OBJ 4)) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)); discriminate
          | unfold spZ at 1 2; rewrite Rsp, F2, unsigned_lit_small by lia; unfold ESTACK; lia ] |];
        split; [ exact (c2_frame_rom_disj ly3 S3 W3 _ _ cx fp _ _ HART Hfin EF HRMB (gF cx fp + GO_MAC) 5
                   ltac:(unfold GO_MAC; lia) ltac:(unfold GO_MAC; lia) ltac:(lia) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)) |];
        split; [ unfold amem_range, kLowMemEnd; lia |];
        split; [ exact HXra | intros _; exact HXhv ] ]
    | ] end.
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout & Hpres2).
    assert (HKA2 : c2_hkeep cx fp W3 r (ms_mem ms3) mem2).
    { apply (c2_hk_trans cx fp W3 r _ (ms_mem msT) mem2 HKA HKA).
      apply (c2_hk_call cx fp W3 r (ms_mem msT) mem2 (gF cx fp + GO_MAC) 5); [lia | lia | | exact HGB2].
      intros a Ha H1 H2. apply Hout; [exact Ha | exact H1 | lia]. }
    clear HKA. rename HKA2 into HKA.
    assert (HM5 : forall j, 0 <= j < 5 -> aview SEGS (w_H W3) mem2 (gF cx fp + GO_MAC + j) =
      Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0)).
    { intros j Hj. rewrite (Heff j Hj). exact (HRT j ltac:(cbn; lia)). }
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
    jafter_call_keep_pi HS 45%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 2; 3; 4]%nat HS2.
    match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val];
        rewrite ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
        intros a Ha;
        first [ (apply (mbyte_of_aview SEGS); apply Hout;
                  unfold GO_MAC, ESTACK, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)
              | (intros _; apply (apresent_writable SEGS); apply HJpres2; unfold GB_STK; lia)
              | lia ]. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E 45 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
    assert (HEIa : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLD1 : forall q, (q < 45)%nat -> ew E1 q = ew E q)
      by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
    clear HE1.
    assert (F2' : ew E1 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F2). clear F2. rename F2' into F2.
    assert (F3' : ew E1 3 = Z_to_bv 64 (as_gp B)) by (rewrite OLD1 by lia; exact F3). clear F3. rename F3' into F3.
    assert (F4' : ew E1 4 = Z_to_bv 64 (as_tp B)) by (rewrite OLD1 by lia; exact F4). clear F4. rename F4' into F4.
    assert (F8' : ew E1 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact F8). clear F8. rename F8' into F8.
    assert (F9' : ew E1 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F9). clear F9. rename F9' into F9.
    assert (F18' : ew E1 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD1 by lia; exact F18). clear F18. rename F18' into F18.
    assert (F20' : ew E1 20 = Z_to_bv 64 r) by (rewrite OLD1 by lia; exact F20). clear F20. rename F20' into F20.
    assert (F24' : ew E1 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite OLD1 by lia; exact F24). clear F24. rename F24' into F24.
    assert (F25' : ew E1 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite OLD1 by lia; exact F25). clear F25. rename F25' into F25.
    assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite OLD1 by lia; exact F32). clear F32. rename F32' into F32.
    assert (F33' : ew E1 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite OLD1 by lia; exact F33). clear F33. rename F33' into F33.
    assert (F36' : ew E1 36 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (r + 280))) by (rewrite OLD1 by lia; exact F36).
    clear F36. rename F36' into F36.
    assert (F38' : ew E1 38 = Z_to_bv 64 (gF cx fp)) by (rewrite OLD1 by lia; exact F38). clear F38. rename F38' into F38.
    assert (FB' : forall j, (j < 6)%nat -> ew E1 (39 + j) = w64 (nth j (c2h_bytes cx pos) 0))
      by (intros j Hj; rewrite OLD1 by lia; exact (FB j Hj)). clear FB. rename FB' into FB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
    pose proof (st_ok_pi_add_region E1 _ _ (c2_frame c2_mac5 37 38) HS eq_refl
      (c2_frameA_ok cx fp E1 W3 mem2 ly3 S3 md2 (proj1 HJ2) Hfin EF F38 HF0 ltac:(lia) HM5)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, c2_frame; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
            rewrite ?F38, ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
            repeat split; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)) as HS1.
    clear HS. rename HS1 into HS.
    assert (SHOK1 : sh_ok SEGS c2_Bx (c2h_SH 5) E1 (mrestrict (w_H W3) mem2)).
    { apply (c2h_sh_gen cx fp pos 5 E1 W3 mem2 F18 F38 F32).
      + lia.
      + destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia.
      + pose proof (gb_mac_ra B MT LAWS cx fp W3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) ly3 S3 md2 k HB HJ2 HFR 0 6
          (c2_hk_gshadow cx fp W3 r ms3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) HKA HSHF HSHh HSH) ltac:(lia) ltac:(lia)) as Hra.
        replace (gF cx fp + GO_MAC + 0) with (gF cx fp + 32) in Hra by (unfold GO_MAC; lia). exact Hra.
      + exact HFapp.
      + intros _. destruct Hinp as [(Hn0 & _) | (_ & Hin3 & Hp4 & Hpce & Hpia & _)]; [lia|].
        split.
        * pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
          apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hin3); lia.
        * unfold in_app in Hpia. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
    clear SHOK HJ. rename SHOK1 into SHOK. rename HJ2 into HJ.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr2 F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 1 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 1) bs ms3 msF md3 _ [0; 64; 171; 0; 0; nth 0 (c2h_bytes cx pos) 0]
      HK HB HFR HBLK HINV HMO Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * reflexivity.
    * constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|].
      constructor; [apply c2h_bytes_nth_rng | constructor].
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 0%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ (cbn [sv_denot]; reflexivity)
                | (apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB 0%nat ltac:(lia)) | apply c2_valsA_rng])
                | (cbn [sv_denot]; rewrite (c2h_bytes_out cx pos 0) by lia; reflexivity) ]
        | apply c2_valsA_rng ]).
- (* kk = 6 *)
  paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
  c2h_keep HKA F9 F38 HGB.
  psrr_branch_tok RUN BR HS SHOK c2_span.
  + (* op & 4 <> 0: the six-byte loop *)
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 6 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 6) bs ms3 msF md3 _ (c2h_bytes cx pos) HK HB HFR HBLK HINV HMO
      Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 0%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * exact Hbl.
    * apply c2h_bytes_rng.
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      lazymatch goal with |- aview _ _ _ (_ + (32 + ?jz)) = _ =>
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 1%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB (Z.to_nat jz) ltac:(lia)) | apply c2h_bytes_nth_rng]
                | cbn [sv_denot]; rewrite (c2h_bytes_out cx pos (Z.to_nat jz)) by lia; reflexivity ]
        | apply c2h_bytes_nth_rng ]) end.
  + (* op & 4 = 0: memcpy (read_mac.base, 5 bytes), then one input byte *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c2_span; [c2h_awr F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msT end.
    pose proof (c2_hk_gshadow cx fp W3 r ms3 msT HKA HSHF HSHh HSH) as HSHT.
    pmkst HS.
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
    pose proof HJ as (HART & _).
    pose proof (c2_rom B MT cx W3 HB (VAL (A_OBJ 4)) [0; 64; 171; 0; 0] _ _ _ _ _ _ HRMB HJ) as HRT.
    destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem msT) _ (VAL (A_OBJ 4)) 5 (VAL (A_OBJ 4)) 5
      HGLOB ltac:(unfold BX_G; right; right; left; reflexivity) HISV HART ltac:(lia) ltac:(lia) ltac:(lia) HM1 HM2)
      as [HXra HXhv].
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
    eapply SRr_bind;
    [ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA BS___asan_memcpy) AMEMCPY W3 rg mm
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (gF cx fp + GO_MAC) (VAL (A_OBJ 4)) 5 (c_sp1 cx - spZ (c_regs cx)) _ HJ);
      [ rewrite Ra0, F38, unsigned_lit_small by lia; reflexivity
      | rewrite Ra1; change 245%nat with (A_OBJ 4); apply (img_env_atomP E (A_OBJ 4) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia
      | rewrite Ra2; reflexivity
      | lia | unfold GO_MAC; lia | unfold GO_MAC; lia
      | unfold spZ at 1; rewrite Rsp, F2, unsigned_lit_small by lia; lia
      | exact Ho16
      | lia
      | unfold ESTACK, GB_STK; lia
      | rewrite Rgp, F3; reflexivity
      | rewrite Rtp, F4; reflexivity
      | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; right; right; exists GB_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; rewrite EF;
          change (fs_frame_bytes GB_CID) with 512; cbn [fst snd]; unfold GO_MAC in *; lia
        | unfold ESTACK, GO_MAC in *; lia ]
      | unfold amem_range; unfold in_app in HFia; unfold GO_MAC, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *; lia
      | pose proof (gb_mac_ra B MT LAWS cx fp W3 msT ly3 S3 _ k HB HJ HFR 0 5 HSHT ltac:(lia) ltac:(lia)) as Hra;
        rewrite Z.add_0_r in Hra; exact Hra
      | intros _; apply (shadow_hull_vis_of_frame _ _ LAWS _ _ _ _ _ GB_CID fp _ _ HART ltac:(rewrite HFR; left; reflexivity));
        try rewrite EF; change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia;
            rewrite (HRT (a - VAL (A_OBJ 4)) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)); discriminate
          | unfold spZ at 1 2; rewrite Rsp, F2, unsigned_lit_small by lia; unfold ESTACK; lia ] |];
        split; [ exact (c2_frame_rom_disj ly3 S3 W3 _ _ cx fp _ _ HART Hfin EF HRMB (gF cx fp + GO_MAC) 5
                   ltac:(unfold GO_MAC; lia) ltac:(unfold GO_MAC; lia) ltac:(lia) ltac:(change (Z.of_nat (length [0; 64; 171; 0; 0])) with 5; lia)) |];
        split; [ unfold amem_range, kLowMemEnd; lia |];
        split; [ exact HXra | intros _; exact HXhv ] ]
    | ] end.
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout & Hpres2).
    assert (HKA2 : c2_hkeep cx fp W3 r (ms_mem ms3) mem2).
    { apply (c2_hk_trans cx fp W3 r _ (ms_mem msT) mem2 HKA HKA).
      apply (c2_hk_call cx fp W3 r (ms_mem msT) mem2 (gF cx fp + GO_MAC) 5); [lia | lia | | exact HGB2].
      intros a Ha H1 H2. apply Hout; [exact Ha | exact H1 | lia]. }
    clear HKA. rename HKA2 into HKA.
    assert (HM5 : forall j, 0 <= j < 5 -> aview SEGS (w_H W3) mem2 (gF cx fp + GO_MAC + j) =
      Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0)).
    { intros j Hj. rewrite (Heff j Hj). exact (HRT j ltac:(cbn; lia)). }
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
    jafter_call_keep_pi HS 45%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 2; 3; 4]%nat HS2.
    match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val];
        rewrite ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
        intros a Ha;
        first [ (apply (mbyte_of_aview SEGS); apply Hout;
                  unfold GO_MAC, ESTACK, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)
              | (intros _; apply (apresent_writable SEGS); apply HJpres2; unfold GB_STK; lia)
              | lia ]. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E 45 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
    assert (HEIa : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLD1 : forall q, (q < 45)%nat -> ew E1 q = ew E q)
      by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
    clear HE1.
    assert (F2' : ew E1 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F2). clear F2. rename F2' into F2.
    assert (F3' : ew E1 3 = Z_to_bv 64 (as_gp B)) by (rewrite OLD1 by lia; exact F3). clear F3. rename F3' into F3.
    assert (F4' : ew E1 4 = Z_to_bv 64 (as_tp B)) by (rewrite OLD1 by lia; exact F4). clear F4. rename F4' into F4.
    assert (F8' : ew E1 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact F8). clear F8. rename F8' into F8.
    assert (F9' : ew E1 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F9). clear F9. rename F9' into F9.
    assert (F18' : ew E1 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD1 by lia; exact F18). clear F18. rename F18' into F18.
    assert (F20' : ew E1 20 = Z_to_bv 64 r) by (rewrite OLD1 by lia; exact F20). clear F20. rename F20' into F20.
    assert (F24' : ew E1 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite OLD1 by lia; exact F24). clear F24. rename F24' into F24.
    assert (F25' : ew E1 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite OLD1 by lia; exact F25). clear F25. rename F25' into F25.
    assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite OLD1 by lia; exact F32). clear F32. rename F32' into F32.
    assert (F33' : ew E1 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite OLD1 by lia; exact F33). clear F33. rename F33' into F33.
    assert (F36' : ew E1 36 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (r + 280))) by (rewrite OLD1 by lia; exact F36).
    clear F36. rename F36' into F36.
    assert (F38' : ew E1 38 = Z_to_bv 64 (gF cx fp)) by (rewrite OLD1 by lia; exact F38). clear F38. rename F38' into F38.
    assert (FB' : forall j, (j < 6)%nat -> ew E1 (39 + j) = w64 (nth j (c2h_bytes cx pos) 0))
      by (intros j Hj; rewrite OLD1 by lia; exact (FB j Hj)). clear FB. rename FB' into FB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
    pose proof (st_ok_pi_add_region E1 _ _ (c2_frame c2_mac5 37 38) HS eq_refl
      (c2_frameA_ok cx fp E1 W3 mem2 ly3 S3 md2 (proj1 HJ2) Hfin EF F38 HF0 ltac:(lia) HM5)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, c2_frame; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
            rewrite ?F38, ?F9, ?F20, ?F36, ?F32, ?unsigned_lit_small by lia;
            repeat split; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)) as HS1.
    clear HS. rename HS1 into HS.
    assert (SHOK1 : sh_ok SEGS c2_Bx (c2h_SH 6) E1 (mrestrict (w_H W3) mem2)).
    { apply (c2h_sh_gen cx fp pos 6 E1 W3 mem2 F18 F38 F32).
      + lia.
      + destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia.
      + pose proof (gb_mac_ra B MT LAWS cx fp W3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) ly3 S3 md2 k HB HJ2 HFR 0 6
          (c2_hk_gshadow cx fp W3 r ms3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS)) HKA HSHF HSHh HSH) ltac:(lia) ltac:(lia)) as Hra.
        replace (gF cx fp + GO_MAC + 0) with (gF cx fp + 32) in Hra by (unfold GO_MAC; lia). exact Hra.
      + exact HFapp.
      + intros _. destruct Hinp as [(Hn0 & _) | (_ & Hin3 & Hp4 & Hpce & Hpia & _)]; [lia|].
        split.
        * pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
          apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hin3); lia.
        * unfold in_app in Hpia. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
    clear SHOK HJ. rename SHOK1 into SHOK. rename HJ2 into HJ.
    paj_run_to_tok RUNTO HS HJ SHOK c2_span GP_F; [c2h_awr2 F9 F38 EF |].
    c2h_keep HKA F9 F38 HGB.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
    lazymatch goal with |- SRr _ _ (mkCfg ?msN _) _ => rename msN into msF end.
    prreg HS (2%bv : bv 5) K2. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
    prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (18%bv : bv 5) K18.
    prreg HS (24%bv : bv 5) K24. prreg HS (20%bv : bv 5) K20. prreg HS (21%bv : bv 5) K21.
    prreg HS (25%bv : bv 5) K25.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HmsF.
    assert (Hcp : 0 <= c_p cx + pos /\ c_p cx + pos + 1 <= 2 ^ 63).
    { destruct Hinp as [(Hn0 & Hpe) | (_ & _ & Hp4 & Hpce & _)]; unfold GB_EMPTY in *; lia. }
    apply (c2_fin i cx fp k acc ly3 S3 W3 r (pos + 1) bs ms3 msF md3 _ [0; 64; 171; 0; 0; nth 0 (c2h_bytes cx pos) 0]
      HK HB HFR HBLK HINV HMO Hk Hacc Hi64 HJ0 HSV HSH HFL HSFR HSLR HS68 HREG HPREV HIN HKA HJ HmsF).
    * rewrite K2; exact F2.
    * rewrite K8; exact F8.
    * rewrite K9; exact F9.
    * rewrite K3, F3; symmetry; exact Hgp0.
    * rewrite K4, F4; symmetry; exact Htp0.
    * rewrite K18; exact F18.
    * rewrite K24; exact F24.
    * rewrite K20; exact F20.
    * rewrite K21, F38, unsigned_lit_small by lia; reflexivity.
    * rewrite K25; exact F25.
    * split; [lia|]. split.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 136 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F32, unsigned_lit_small by lia. f_equal. lia.
      -- eapply (c2_slot_read cx W3 i Hi64 _ _ _ _ _ msF 1%nat _ _ _ _ _ 144 _);
           [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F9; apply unsigned_lit_small; lia
           | cbn; repeat first [left; reflexivity | right] | | lia].
         cbn [sv_denot ew ewset Nat.eqb]. rewrite F33, unsigned_lit_small by lia. f_equal. lia.
    * reflexivity.
    * constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|]. constructor; [lia|].
      constructor; [apply c2h_bytes_nth_rng | constructor].
    * intros j Hj.
      replace (gF cx fp + GO_MAC + j) with (gF cx fp + (32 + j)) by (unfold GO_MAC; lia).
      assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
      destruct Hjs as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (eapply (c2_mac_read cx fp W3 i Hi64 _ _ _ _ _ msF 0%nat);
        [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; rewrite F38; apply unsigned_lit_small; lia
        | cbn; repeat first [left; reflexivity | right]
        | first [ (cbn [sv_denot]; reflexivity)
                | (apply c2_den_zext; [cbn [ew ewset Nat.eqb]; exact (FB 0%nat ltac:(lia)) | apply c2_valsA_rng])
                | (cbn [sv_denot]; rewrite (c2h_bytes_out cx pos 0) by lia; reflexivity) ]
        | apply c2_valsA_rng ]).
Qed.

End Top.
