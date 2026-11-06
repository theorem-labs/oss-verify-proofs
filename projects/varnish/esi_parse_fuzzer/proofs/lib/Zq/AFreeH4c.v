(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 AMTac ARt2_lib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt22wr AFreeH AFreeH0 AFreeHc AFreeH2c AFreeH3c ARtS4t2 AFreeH4w AFreeH4r.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt23oh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2hw4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22wr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH2c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH3c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH4w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH4r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition natz_boxed (P : Prop) : Prop := P.
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.
Local Ltac natz_kl_box :=
  try (lazymatch goal with
       | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
           let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
           natz_z_lit za; natz_z_lit zb;
           let Hz := fresh "KLz" in
           pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz;
           change (natz_boxed (a <= @length A l <= b)%nat) in H
       | H : (@length ?A ?l <= ?b)%nat |- _ =>
           let zb := eval vm_compute in (Z.of_nat b) in
           natz_z_lit zb;
           let Hz := fresh "KLz" in
           pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz;
           change (natz_boxed (@length A l <= b)%nat) in H
       end).
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].


(* [comment removed for export] *)
Definition free_ccore_new0F_W (spd : word) (thr b ri : Z) : list (Z * Z) :=
  (bv_unsigned spd + -80 - 224, bv_unsigned spd + -80)
  :: [(thr + 80, thr + 112); (thr + 208 + 1920, thr + 208 + 2000); (thr + 208 + 2576, thr + 208 + 2584); (b, b + 32);
      (ri + 3072, ri + 3080); (ri + 3088, ri + 3096); (ri + 3144, ri + 3152)].
Definition free_chit_new0F_W (spd : word) (lo thr p r8 n0 f0 : Z) (b ri : Z) : list (Z * Z) :=
  free_cprefix_W spd thr p r8 n0 f0 ++ [(thr + 80, thr + 112); (thr + 208 + 1920, thr + 208 + 2000); (thr + 208 + 2576, thr + 208 + 2584); (b, b + 32);
      (ri + 3072, ri + 3080); (ri + 3088, ri + 3096); (ri + 3144, ri + 3152)].
Definition free_ccore_newfullF_W (spd : word) (thr b ri lb : Z) : list (Z * Z) :=
  (bv_unsigned spd + -80 - 224, bv_unsigned spd + -80)
  :: [(thr + 80, thr + 112); (lb, lb + 8); (thr + 208 + 1920, thr + 208 + 2000); (thr + 208 + 2576, thr + 208 + 2584); (b, b + 32);
      (ri + 3072, ri + 3080); (ri + 3088, ri + 3096); (ri + 3144, ri + 3152)].
Definition free_chit_newfullF_W (spd : word) (lo thr p r8 n0 f0 : Z) (b ri lb : Z) : list (Z * Z) :=
  free_cprefix_W spd thr p r8 n0 f0 ++ [(thr + 80, thr + 112); (lb, lb + 8); (thr + 208 + 1920, thr + 208 + 2000); (thr + 208 + 2576, thr + 208 + 2584); (b, b + 32);
      (ri + 3072, ri + 3080); (ri + 3088, ri + 3096); (ri + 3144, ri + 3152)].

(* [comment removed for export] *)
Ltac sub_fp_negs_clear := repeat match goal with H : ~ _ |- _ => clear H end.
Ltac sub_fp_fast :=
  unfold sub_fp; cbn [outside]; intros y Hy;
  repeat (lazymatch type of Hy with _ /\ _ => let H := fresh "HO" in destruct Hy as [H Hy] end);
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I | assumption
        | lazymatch goal with |- ~ (?lo <= ?a < ?hi) =>
            multimatch goal with H : ~ (?lo' <= a < ?hi') |- _ =>
              apply (notin_mono a lo hi lo' hi' H); sub_fp_negs_clear; lia end end
        | lia ].

Section FreeHitCore.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto : Z) (D : list (list Z)) (key : list Z) (old : word) (oldsh : list byte).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned spd).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned spd - 704.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis SPH : bv_unsigned spd <= 2^47.
  Hypothesis RA2 : bv_unsigned rac mod 2 = 0.
  Hypothesis TPE : tp = Z_to_bv 64 TP.
  (* [comment removed for export] *)
  Hypothesis PAL : p mod 16 = 0.
  Hypothesis PLO : aobj (p + -16) (16 + 8 * r8).   (* [comment removed for export] *)
  Hypothesis PNB : 0x60a000 <= p + -16.             (* [comment removed for export] *)
  Hypothesis PHI : p + 8 * r8 <= alloc_ceiling.
  Hypothesis NR : 1 <= n < 2^32.
  Hypothesis NQ : n <= 2^28.
  Hypothesis R8 : 8 * r8 - 8 < n <= 8 * r8.
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 3 = 1.
  Hypothesis HDR : rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)].
  Hypothesis CTX0 : rw_cells rsegs m p [C8 old].
  Hypothesis SHC : rw_cells rsegs m (sh p) [CB (Z.to_nat r8) oldsh].
  (* [comment removed for export] *)
  Hypothesis FCo : free_consts m.
  Hypothesis PCo : poison_consts m.
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (wz ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (wz kMainTid)].
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TST : rw_cells rsegs m (thr + 2824) [C8 (wz fr); C8 (wz fd)].
  Hypothesis FRR : 0 <= fr < 2^64.
  Hypothesis FDR : 0 <= fd < 2^64.
  (* [comment removed for export] *)
  Hypothesis DR : depot_repL AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 256 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis STO : ro_cells rsegs m sto [C8 (wz (sto + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRW : bytes_at rsegs m (sto + 16) (u64s (map (Z_to_bv 64) key)).
  Hypothesis STOR : bv_unsigned spd <= sto /\ sto + 2064 <= 2^47.
  Hypothesis KL : (1 <= length key <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
  (* [comment removed for export] *)
  Hypothesis SEP_pc : apart (p + -16) (8 * r8 + 16) ctx 0x10000.
  Hypothesis SEP_pt : apart (p + -16) (8 * r8 + 16) thr 4096.
  Hypothesis SEP_pn : apart (p + -16) (8 * r8 + 16) n0 kDepotNodesBlock.
  Hypothesis SEP_pf : apart (p + -16) (8 * r8 + 16) f0 kStackStoreBlockBytes.
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned spd).
  Let D' : list (list Z) := fst (depot_putC D key).
  Let fid : Z := snd (depot_putC D key).

  (* [comment removed for export] *)
  Let PREFIX := free_cprefix rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto D key old oldsh MI ST LO RA2 TPE PAL PLO PNB PHI NR NQ R8 B1R B1M HDR CTX0 SHC FCo PCo TC TH0 CT8 TSDL TST FRR FDR
    DR DND DLEN DTOT DN0 DF0 STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc.
  Let PTAIL := free_cptail rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p tsd ctx thr r8 n0 f0 sto D key LO SPH PLO PNB TC DN0 DF0 KL.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (sb ri nf : Z) (w na : word).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 3072).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (free_array_of sb 24).
  #[warnings="-notation-for-abbreviation"] Local Notation b := (sb + 24 * 2^32 + 16 * bv_unsigned w).
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_ts : apart thr 4096 sb (2^37).
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_rp : apart ri 4096 (p + -16) (8 * r8 + 16).
  Hypothesis SEP_rc : apart ri 4096 ctx 0x10000.
  Hypothesis SEP_rn : apart ri 4096 n0 kDepotNodesBlock.
  Hypothesis SEP_rf : apart ri 4096 f0 kStackStoreBlockBytes.
  Hypothesis SEP_ns : apart n0 kDepotNodesBlock sb (2^37).
  Hypothesis SEP_fs : apart f0 kStackStoreBlockBytes sb (2^37).
  Hypothesis Afap : apart (sb + 24 * 2^32 + 3758096384) (4 * 2^27) (p + -16) (8 * r8 + 16).   (* [comment removed for export] *)
  Hypothesis WR : bv_unsigned w < 2^32.
  Hypothesis NFR : 1 <= nf < 2^27.
  Hypothesis BLO : kHighMemBeg <= b.
  Hypothesis BHI : b + 8192 <= alloc_ceiling.
  Hypothesis BFA : b + 8192 <= fa.
  Hypothesis Abt : apart b 8192 thr 4096.
  Hypothesis Abp : apart b 8192 (p + -16) (8 * r8 + 16).
  Hypothesis Abc : apart b 8192 ctx 0x10000.
  Hypothesis Abn : apart b 8192 n0 kDepotNodesBlock.
  Hypothesis Abf : apart b 8192 f0 kStackStoreBlockBytes.
  Hypothesis Abr : apart b 8192 ri 4096.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_cenq_new0F_post (fb lb qb : Z) (ks : list word) (m6 : word -> option byte) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word) (m' : word -> option byte),
    ms' = (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                 a0' a1' a2' a3' a4' a5' a6' a7' (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20))
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x3b60c) fc None m' (seg_rom rsegs))
    /\ munch (free_ccore_new0F_W spd thr b ri) m6 m'
    /\ wmono rsegs m6 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (usp + -80)
    /\ rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' (thr + 80) [C8 (wz 1); C8 (wz b); C8 (wz b); C8 (wz (qb + (n + 8192)))]
    /\ rw_cells rsegs m' (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))]
    /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv']
    /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (n + 8192)); C8 (wz 1); C8 (wz (p + -16))]
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf - 1))]
    /\ rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))]
    /\ u32arr rsegs m' (fa + 4 * (nf - 1)) [w].

  (* [comment removed for export] *)
  #[using="Abf Abn Abp Abt BFA BHI BLO NFR WR SEP_rf SEP_rn SEP_rp SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBAL SBHI SBLO SEP_f0t SEP_n0t SEP_pt KL STOR DF0 DN0 TC R8 NR PNB PLO PAL SPH SPA LO ctx tsd m Clg"] Lemma free_cenq_new0F : forall (fb lb qb : Z) (ks : list word) (statv bj0 bj1 bj2 bj3 : word) (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m6 : word -> option byte),
    0 <= qb -> qb + (n + 8192) < 2^64 -> thr mod 16 = 0 -> length ks = 16%nat ->
    ro_cells rsegs m6 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m6 0xb1588 [C8 (wz ri)] ->
    rw_cells rsegs m6 (thr + 80) [C8 (wz 0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m6 (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m6 (thr + 208 + 2576) [C8 statv] ->
    rw_cells rsegs m6 R [C8 (wz 0)] -> rw_cells rsegs m6 (R + 16) [C8 (wz nf)] -> rw_cells rsegs m6 (R + 72) [C8 na] ->
    u32arr rsegs m6 (fa + 4 * (nf - 1)) [w] ->
    rw_cells rsegs m6 b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    rw_cells rsegs m6 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    rw_cells rsegs m6 (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
    rw_cells rsegs m6 (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m6 p [C8 (wz fid)] ->
    bytes_at rsegs m6 (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
    depot_repL AL_pboth rsegs D' n0 f0 m6 ->
    mem_inv rsegs m6 -> stk rsegs m6 lo (usp - 80) ->
    evt rsegs (free_cenq_new0F_post fb lb qb ks m6)
        (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                            (wz (thr + 80)) (wz (thr + 208)) (wz sto) (wz (p + -16)) (wz n) a5' a6' a7'
                            (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz enqueue_entry) fc None m6 (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros fb lb qb ks statv bj0 bj1 bj2 bj3 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' m6.
    intros QB0 QBN THRA LKS SBC RIC QC PC24 STA MXc NFCc NALc FARRc BC PFR TST6 HDR6 CTX6 SHD6 DR6 MI6 ST6.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold off_th_unwinding, enqueue_entry, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *. rewrite SHF in SHD6.
    box LKS || idtac.
    pose proof (munch_refl (free_ccore_new0F_W spd thr b ri) m6) as MU. unfold free_ccore_new0F_W in MU. pose proof (wmono_refl rsegs m6) as WM.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (enq_refill_new0 _ (wz (usp + -80)) gp tp t0' t1' t2' _ _ a5' a6' a7' _ _ _ _ _ s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m6
                               lo (thr + 80) (thr + 208) sto (p + -16) n fb lb qb 0 0 sb ri nf ks w statv na bj0 bj1 bj2 bj3)|];
      cbv zeta; [> try (fside CV) .. | idtac].
    all: try (unfold boxed in *; assumption).
    all: try (lazymatch goal with |- apart _ _ _ _ =>
                first [ revert SEP_tr; unfold apart; clear; intros; lia | revert SEP_ts; unfold apart; clear; intros; lia
                      | revert Abt; unfold apart; clear; intros; lia ] end).
    all: try (rewrite ?unsigned_lit by lia; apply mod_add_lit; [lia | assumption | reflexivity]).   (* [comment removed for export] *)
    intros ms' PO. unfold enq_refill_post0, enq_refill_W0 in PO. cbv zeta in PO. destruct_exs PO.
    (first [ dand13 PO as E MUc WMc MI7 ST7 QC7 PC7 STA7 BC7 MX7 NFC7 NAL7 FARR7 | destruct PO as (E & MUc & WMc & MI7 & ST7 & QC7 & PC7 & STA7 & BC7 & MX7 & NFC7 & NAL7 & FARR7) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST7 by lia.
    eapply bytes_at_transport in SHD6; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; unfold apart in Abp, SEP_rp; lia].
    clear SBC RIC QC PC24 STA BC MXc NFCc NALc FARRc. xdepot DR6 MUc. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x3b60c)) with (Z_to_bv 64 0x3b60c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply evt_done. unfold free_cenq_new0F_post, free_ccore_new0F_W, off_th_unwinding, QINST. cbv zeta. rewrite SHF.
    hot_eexists_all. split; [reflexivity|].
    unfold boxed in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; eassumption.
  Qed.

  Definition free_chead_new0F_post (fb lb qb : Z) (ks : list word) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word) (m' : word -> option byte),
    ms' = (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                 a0' a1' a2' a3' a4' a5' a6' a7' (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20))
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x3b60c) fc None m' (seg_rom rsegs))
    /\ munch (free_chit_new0F_W spd lo thr p r8 n0 f0 b ri) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (usp + -80)
    /\ rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' (thr + 80) [C8 (wz 1); C8 (wz b); C8 (wz b); C8 (wz (qb + (n + 8192)))]
    /\ rw_cells rsegs m' (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))]
    /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv']
    /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (n + 8192)); C8 (wz 1); C8 (wz (p + -16))]
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf - 1))]
    /\ rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))]
    /\ u32arr rsegs m' (fa + 4 * (nf - 1)) [w].

  (* [comment removed for export] *)
  #[using="Abf Abn Abp Abt BFA BHI BLO NFR WR Afap SEP_fs SEP_ns SEP_rf SEP_rn SEP_rp SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBAL SBHI SBLO PREFIX SEP_tc SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_pf SEP_pn SEP_pt SEP_pc KR KL STOR TRW STO DF0 DN0 DTOT DLEN DND DR FDR FRR TST TSDL CT8 TH0 TC PCo FCo SHC CTX0 HDR B1M B1R R8 NQ NR PHI PNB PLO PAL TPE RA2 SPH SPA LO ST MI oldsh old ctx tsd Clg"] Lemma free_chead_new0F : forall (fb lb qb : Z) (ks : list word) (statv bj0 bj1 bj2 bj3 : word),
    0 <= qb -> qb + (n + 8192) < 2^64 -> thr mod 16 = 0 -> length ks = 16%nat ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m 0xb1588 [C8 (wz ri)] ->
    rw_cells rsegs m (thr + 80) [C8 (wz 0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (thr + 208 + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] -> rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 72) [C8 na] ->
    u32arr rsegs m (fa + 4 * (nf - 1)) [w] ->
    rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    evt rsegs (free_chead_new0F_post fb lb qb ks)
        (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz AINST) (wz p) a2 a3 (wz sto) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz dealloc_entry) fc None m (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros fb lb qb ks statv bj0 bj1 bj2 bj3. intros QB0 QBN THRA LKS SBC RIC QC PC24 STA MXc NFCc NALc FARRc BC.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *.
    apply PREFIX. intros t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' m6 PFR TST6 HDR6 CTX6 SHD6 DR6 MU6 WM6 MI6 ST6.
    unfold free_cprefix_W, off_th_unwinding, enqueue_entry in *. rewrite SHF in MU6.
    xfer SBC MU6 WM6. xfer RIC MU6 WM6. xfer QC MU6 WM6. xfer PC24 MU6 WM6. xfer STA MU6 WM6. xfer BC MU6 WM6.
    xfer MXc MU6 WM6. xfer NFCc MU6 WM6. xfer NALc MU6 WM6.
    unfold free_array_of in FARRc.
    lazymatch type of MU6 with munch ?W ?mi ?mc =>
      apply (u32arr_transport rsegs W mi mc) in FARRc; [| exact MU6| exact WM6| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia] end.
    eapply evt_cut; [eapply (free_cenq_new0F fb lb qb ks statv bj0 bj1 bj2 bj3 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' m6); cbv zeta;
                     first [eassumption | unfold off_th_unwinding; eassumption | kung; lia | rewrite SHF; eassumption | unfold free_array_of; eassumption] |].
    intros ms' PO. unfold free_cenq_new0F_post in PO. cbv zeta in PO. destruct_exs PO.
    (first [ dand4 PO as E MUc WMc PO | destruct PO as (E & MUc & WMc & PO) ]). subst ms'. apply evt_done. unfold free_chead_new0F_post. cbv zeta.
    hot_eexists_all. split; [reflexivity|].
    split. { unfold free_chit_new0F_W, free_cprefix_W, free_ccore_new0F_W in *. rewrite SHF. rewrite ?unsigned_lit in MUc by lia. cbn [app].
             eapply munch_trans; [eapply munch_weaken; [| exact MU6] | eapply munch_weaken; [| exact MUc]]; sub_fp_fast. }
    split. { eapply wmono_trans; [exact WM6 | exact WMc]. }
    exact PO.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_cenq_newfullF_post (nb fb lb qb bsz : Z) (ks : list word) (m6 : word -> option byte) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word) (m' : word -> option byte),
    ms' = (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                 a0' a1' a2' a3' a4' a5' a6' a7' (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20))
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x3b60c) fc None m' (seg_rom rsegs))
    /\ munch (free_ccore_newfullF_W spd thr b ri lb) m6 m'
    /\ wmono rsegs m6 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (usp + -80)
    /\ rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' (thr + 80) [C8 (wz (nb + 1)); C8 (wz fb); C8 (wz b); C8 (wz (qb + (n + 8192)))]
    /\ rw_cells rsegs m' lb [C8 (wz b); C8 (wz bsz); C8 (wz 1021)]
    /\ rw_cells rsegs m' (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))]
    /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv']
    /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (n + 8192)); C8 (wz 1); C8 (wz (p + -16))]
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf - 1))]
    /\ rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))]
    /\ u32arr rsegs m' (fa + 4 * (nf - 1)) [w].

  (* [comment removed for export] *)
  #[using="Abf Abn Abp Abt BFA BHI BLO NFR WR SEP_rf SEP_rn SEP_rp SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBAL SBHI SBLO SEP_f0t SEP_n0t SEP_pt KL STOR DF0 DN0 TC R8 NR PNB PLO PAL SPH SPA LO tsd m"] Lemma free_cenq_newfullF : forall (nb fb lb qb nx bsz : Z) (ks : list word) (statv bj0 bj1 bj2 bj3 : word) (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m6 : word -> option byte),
    nb <> 0 -> 0 <= nb < 2^63 -> 0 <= qb -> qb + (n + 8192) < 2^64 -> thr mod 16 = 0 -> length ks = 16%nat ->
    kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling -> lb + 8192 <= fa ->
    apart lb 8192 thr 4096 -> apart lb 8192 (p + -16) (8 * r8 + 16) -> apart lb 8192 ctx 0x10000 ->
    apart lb 8192 n0 kDepotNodesBlock -> apart lb 8192 f0 kStackStoreBlockBytes -> apart lb 8192 ri 4096 -> apart b 8192 lb 8192 ->
    ro_cells rsegs m6 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m6 0xb1588 [C8 (wz ri)] ->
    rw_cells rsegs m6 (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m6 lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    rw_cells rsegs m6 (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m6 (thr + 208 + 2576) [C8 statv] ->
    rw_cells rsegs m6 R [C8 (wz 0)] -> rw_cells rsegs m6 (R + 16) [C8 (wz nf)] -> rw_cells rsegs m6 (R + 72) [C8 na] ->
    u32arr rsegs m6 (fa + 4 * (nf - 1)) [w] ->
    rw_cells rsegs m6 b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    rw_cells rsegs m6 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    rw_cells rsegs m6 (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
    rw_cells rsegs m6 (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m6 p [C8 (wz fid)] ->
    bytes_at rsegs m6 (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
    depot_repL AL_pboth rsegs D' n0 f0 m6 ->
    mem_inv rsegs m6 -> stk rsegs m6 lo (usp - 80) ->
    evt rsegs (free_cenq_newfullF_post nb fb lb qb bsz ks m6)
        (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                            (wz (thr + 80)) (wz (thr + 208)) (wz sto) (wz (p + -16)) (wz n) a5' a6' a7'
                            (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz enqueue_entry) fc None m6 (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros nb fb lb qb nx bsz ks statv bj0 bj1 bj2 bj3 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' m6.
    intros NB NBR QB0 QBN THRA LKS LBLO LBHI LBFA Albt Albp Albc Albn Albf Albr Abl SBC RIC QC LB PC24 STA MXc NFCc NALc FARRc BC PFR TST6 HDR6 CTX6 SHD6 DR6 MI6 ST6.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold off_th_unwinding, enqueue_entry, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *. rewrite SHF in SHD6.
    box LKS || idtac.
    pose proof (munch_refl (free_ccore_newfullF_W spd thr b ri lb) m6) as MU. unfold free_ccore_newfullF_W in MU. pose proof (wmono_refl rsegs m6) as WM.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (enq_refill_newfull _ (wz (usp + -80)) gp tp t0' t1' t2' _ _ a5' a6' a7' _ _ _ _ _ s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m6
                               lo (thr + 80) (thr + 208) sto (p + -16) n fb lb qb nx bsz sb ri nf ks w statv na bj0 bj1 bj2 bj3)|];
      cbv zeta; [> try (fside CV) .. | idtac].
    all: try (unfold boxed in *; assumption).
    all: try (lazymatch goal with |- apart _ _ _ _ =>
                first [ revert SEP_tr; unfold apart; clear; intros; lia | revert SEP_ts; unfold apart; clear; intros; lia
                      | revert Abt; unfold apart; clear; intros; lia | revert Albt; unfold apart; clear; intros; lia
                      | revert Abl; unfold apart; clear; intros; lia ] end).
    all: try (rewrite ?unsigned_lit by lia; apply mod_add_lit; [lia | assumption | reflexivity]).   (* [comment removed for export] *)
    intros ms' PO. unfold enq_refill_postF, enq_refill_WF in PO. cbv zeta in PO. destruct_exs PO.
    (first [ dand14 PO as E MUc WMc MI7 ST7 QC7 LB7 PC7 STA7 BC7 MX7 NFC7 NAL7 FARR7 | destruct PO as (E & MUc & WMc & MI7 & ST7 & QC7 & LB7 & PC7 & STA7 & BC7 & MX7 & NFC7 & NAL7 & FARR7) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST7 by lia.
    eapply bytes_at_transport in SHD6; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; unfold apart in Abp, SEP_rp, Albp; lia].
    clear SBC RIC QC LB PC24 STA BC MXc NFCc NALc FARRc. xdepot DR6 MUc. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x3b60c)) with (Z_to_bv 64 0x3b60c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply evt_done. unfold free_cenq_newfullF_post, free_ccore_newfullF_W, off_th_unwinding, QINST. cbv zeta. rewrite SHF.
    hot_eexists_all. split; [reflexivity|].
    unfold boxed in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; eassumption.
  Qed.

  Definition free_chead_newfullF_post (nb fb lb qb bsz : Z) (ks : list word) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word) (m' : word -> option byte),
    ms' = (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                 a0' a1' a2' a3' a4' a5' a6' a7' (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20))
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x3b60c) fc None m' (seg_rom rsegs))
    /\ munch (free_chit_newfullF_W spd lo thr p r8 n0 f0 b ri lb) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (usp + -80)
    /\ rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' (thr + 80) [C8 (wz (nb + 1)); C8 (wz fb); C8 (wz b); C8 (wz (qb + (n + 8192)))]
    /\ rw_cells rsegs m' lb [C8 (wz b); C8 (wz bsz); C8 (wz 1021)]
    /\ rw_cells rsegs m' (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))]
    /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv']
    /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (n + 8192)); C8 (wz 1); C8 (wz (p + -16))]
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf - 1))]
    /\ rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))]
    /\ u32arr rsegs m' (fa + 4 * (nf - 1)) [w].

  (* [comment removed for export] *)
  #[using="Abf Abn Abp Abt BFA BHI BLO NFR WR Afap SEP_fs SEP_ns SEP_rf SEP_rn SEP_rp SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBAL SBHI SBLO PREFIX SEP_tc SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_pf SEP_pn SEP_pt SEP_pc KR KL STOR TRW STO DF0 DN0 DTOT DLEN DND DR FDR FRR TST TSDL CT8 TH0 TC PCo FCo SHC CTX0 HDR B1M B1R R8 NQ NR PHI PNB PLO PAL TPE RA2 SPH SPA LO ST MI oldsh old tsd"] Lemma free_chead_newfullF : forall (nb fb lb qb nx bsz : Z) (ks : list word) (statv bj0 bj1 bj2 bj3 : word),
    nb <> 0 -> 0 <= nb < 2^63 -> 0 <= qb -> qb + (n + 8192) < 2^64 -> thr mod 16 = 0 -> length ks = 16%nat ->
    kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling -> lb + 8192 <= fa ->
    apart lb 8192 thr 4096 -> apart lb 8192 (p + -16) (8 * r8 + 16) -> apart lb 8192 ctx 0x10000 ->
    apart lb 8192 n0 kDepotNodesBlock -> apart lb 8192 f0 kStackStoreBlockBytes -> apart lb 8192 ri 4096 -> apart b 8192 lb 8192 ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m 0xb1588 [C8 (wz ri)] ->
    rw_cells rsegs m (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    rw_cells rsegs m (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (thr + 208 + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] -> rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 72) [C8 na] ->
    u32arr rsegs m (fa + 4 * (nf - 1)) [w] ->
    rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    evt rsegs (free_chead_newfullF_post nb fb lb qb bsz ks)
        (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz AINST) (wz p) a2 a3 (wz sto) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz dealloc_entry) fc None m (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros nb fb lb qb nx bsz ks statv bj0 bj1 bj2 bj3. intros NB NBR QB0 QBN THRA LKS LBLO LBHI LBFA Albt Albp Albc Albn Albf Albr Abl SBC RIC QC LB PC24 STA MXc NFCc NALc FARRc BC.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *.
    apply PREFIX. intros t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' m6 PFR TST6 HDR6 CTX6 SHD6 DR6 MU6 WM6 MI6 ST6.
    unfold free_cprefix_W, off_th_unwinding, enqueue_entry in *. rewrite SHF in MU6.
    xfer SBC MU6 WM6. xfer RIC MU6 WM6. xfer QC MU6 WM6. xfer LB MU6 WM6. xfer PC24 MU6 WM6. xfer STA MU6 WM6. xfer BC MU6 WM6.
    xfer MXc MU6 WM6. xfer NFCc MU6 WM6. xfer NALc MU6 WM6.
    unfold free_array_of in FARRc.
    lazymatch type of MU6 with munch ?W ?mi ?mc =>
      apply (u32arr_transport rsegs W mi mc) in FARRc; [| exact MU6| exact WM6| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia] end.
    eapply evt_cut; [eapply (free_cenq_newfullF nb fb lb qb nx bsz ks statv bj0 bj1 bj2 bj3 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' m6); cbv zeta;
                     first [eassumption | unfold off_th_unwinding; eassumption | kung; lia | rewrite SHF; eassumption | unfold free_array_of; eassumption] |].
    intros ms' PO. unfold free_cenq_newfullF_post in PO. cbv zeta in PO. destruct_exs PO.
    (first [ dand4 PO as E MUc WMc PO | destruct PO as (E & MUc & WMc & PO) ]). subst ms'. apply evt_done. unfold free_chead_newfullF_post. cbv zeta.
    hot_eexists_all. split; [reflexivity|].
    split. { unfold free_chit_newfullF_W, free_cprefix_W, free_ccore_newfullF_W in *. rewrite SHF. rewrite ?unsigned_lit in MUc by lia. cbn [app].
             eapply munch_trans; [eapply munch_weaken; [| exact MU6] | eapply munch_weaken; [| exact MUc]]; sub_fp_fast. }
    split. { eapply wmono_trans; [exact WM6 | exact WMc]. }
    exact PO.
  Qed.
End FreeHitCore.
