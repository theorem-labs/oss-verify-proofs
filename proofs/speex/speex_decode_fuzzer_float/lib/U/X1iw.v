(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii X1iu X1it.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qz X1r0 X1r3 X1r4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition pagein_null_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo A L Gv G Dsy : Z) (og : page) (shdr hs : list byte) (os : stream_st bptr) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' A (stream_cells 0 L Gv shdr os)
/\ rw_cells rsegs m' G (page_cells Dsy og) /\ bytes_at rsegs m' (Dsy + pg_hdr og) hs.

Lemma ogg_stream_pagein_null_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(lo A L Gv G Dsy : Z) (og : page) (shdr hs : list byte) (os : stream_st bptr),
length shdr = 284%nat -> stream_fields_ok os -> (27 <= length hs)%nat ->
rw_cells rsegs m A (stream_cells 0 L Gv shdr os) ->
rw_cells rsegs m G (page_cells Dsy og) -> bytes_at rsegs m (Dsy + pg_hdr og) hs ->
0 <= Dsy -> 0 <= pg_hdr og -> 0 <= pg_header_len og -> 0 <= pg_body_len og ->
Dsy + pg_hdr og + pg_header_len og < 2^63 ->
mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp ->
bv_unsigned sp <= A -> bv_unsigned sp <= G -> (A + 408 <= G \/ G + 32 <= A) ->
(Dsy + pg_hdr og + Z.of_nat (length hs) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= Dsy + pg_hdr og) ->
evt rsegs (pagein_null_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A L Gv G Dsy og shdr hs os m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_pagein) fc None m (seg_rom rsegs)).
Proof.
intros until os. intros HL FOK LENH OS OG HS HDsy Hpg Hhl Hbl TOPH MI ST LOSP SPA SPG SEP_AG SEP_HF.
unfold A_ogg_stream_pagein.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
unfold page_cells, wz in OG. pose proof (rw_cells_bound _ _ _ _ OG) as GGB. cbn [cells_size csize Nat.add] in GGB.
unfold stream_cells, wz in OS. pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HS as (HB0 & HB1 & HB). pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 144%nat ST.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 rsegs mx (Dsy + pg_hdr og) hs 4 _ HS ltac:(lia) ltac:(lia) eq_refl) as R4;
pose proof (bytes_at_read1 rsegs mx (Dsy + pg_hdr og) hs 5 _ HS ltac:(lia) ltac:(lia) eq_refl) as R5 end.
zstep. zstep. clear R4 R5.

zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
call (ogg_page_granulepos_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx G Dsy og hs) end.
all: try reflexivity. all: try exact OG. all: try exact HS. all: try lia. all: try assumption.
subst.

zstep. zstep. if_cases CA; zify_cond CA; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CA by lia. 1: exfalso; lia.

zstep. zstep. zstep. if_cases CB0; zify_cond CB0; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CB0 by lia.
2: { exfalso. apply CB0. reflexivity. }

zstep.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
match goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -144) ?cs |- _ =>
pose proof (rw_cells_merge rsegs _ _ [] cs [] ltac:(rewrite app_nil_r; exact FRx)) as FRm; clear FRx; cbn [cells_size csize cells_bytes cbytes Nat.add app] in FRm end.
release_frame FRm ST (bv_unsigned sp).
zstep. zstep.
apply evt_done. unfold pagein_null_post.
sf_eexists 14%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST|]. split; [exact OS|]. split; [exact OG| exact HS].
Qed.

Lemma ogg_stream_pagein_null_implM :
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (body : list Z)
(lo A L Gv G Dsy : Z) (og : page) (shdr hs : list byte) (os : stream_st bptr),
os_body_data os = None ->
length shdr = 284%nat -> stream_fields_ok os -> (27 <= length hs)%nat ->
rw_cells rsegs m A (stream_cells 0 L Gv shdr os) ->
rw_cells rsegs m G (page_cells Dsy og) -> bytes_at rsegs m (Dsy + pg_hdr og) hs ->
0 <= Dsy -> 0 <= pg_hdr og -> 0 <= pg_header_len og -> 0 <= pg_body_len og ->
Dsy + pg_hdr og + pg_header_len og < 2^63 ->
mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp ->
bv_unsigned sp <= A -> bv_unsigned sp <= G -> (A + 408 <= G \/ G + 32 <= A) ->
(Dsy + pg_hdr og + Z.of_nat (length hs) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= Dsy + pg_hdr og) ->
implM rsegs (ogg_stream_pagein raw_realloc raw_free os (ubytes hs) body) s
(fun r s' ms' => r = (-1, os) /\ s' = s /\
pagein_null_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A L Gv G Dsy og shdr hs os m ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_pagein) fc None m (seg_rom rsegs)).
Proof.
intros until os. intros Hnone. intros.
unfold ogg_stream_pagein, ogg_stream_check. rewrite Hnone.
apply implM_ret. eapply evt_mono; [eapply ogg_stream_pagein_null_spec; eassumption|].
intros ms' P. split; [reflexivity|]. split; [reflexivity| exact P].
Qed.
