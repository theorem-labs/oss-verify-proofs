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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH0 AFreeT AFreeHc AFreeDc AFreeH3c.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt23oh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeDc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH3c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LKS; @PNB; @LBthr; @SPR; @TOK; @Agt; @NBR; @LO; @GL3; @BLO; @NB0; @LBL; @CV; @PQ; @ADN0; @ADF0; @BHI; @NR; @QBN; @LBH; @Alt; @Abt; @R8; @Agp; @GL1; @Agl; @Agb; @QB0; @GL2; @Agn; @Agf; @LPLO])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
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
Definition free_coreG_newfull_W (thr lb b : Z) : list (Z * Z) :=
  [(thr + 80, thr + 112); (lb, lb + 8); (thr + 208 + 1920, thr + 208 + 1924); (thr + 208 + 2576, thr + 208 + 2584); (b, b + 32)].
Definition free_chitG_newfull_W (tk : ftail) (spd : word) (thr p r8 n0 f0 lb b gl : Z) : list (Z * Z) :=
  free_cprefix_W spd thr p r8 n0 f0 ++ free_coreG_newfull_W thr lb b ++ ctail_W tk spd thr gl.

Lemma munch_sets : forall W W' (ma mb : mem), munch W ma mb -> (forall x, outside W' x -> outside W x) -> munch W' ma mb.
Proof. intros W W' ma mb M S x Hx. apply M, S, Hx. Qed.

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
  Let HEAD := free_chead_newfull rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto D key old oldsh MI ST LO SPH RA2 TPE PAL PLO PNB PHI NR NQ R8 B1R B1M HDR CTX0 SHC FCo PCo TC TH0 CT8 TSDL TST FRR FDR
    DR DND DLEN DTOT DN0 DF0 STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc.
  Let PTAIL := free_cptail rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p tsd ctx thr r8 n0 f0 sto D key LO SPH PLO PNB TC DN0 DF0 KL.
  Let DTAIL0 := free_cdtail0 rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto D key
    LO SPH PAL PLO PNB NR R8 TC DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t.
  Let DTAILA := free_cdtailA rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto D key
    LO SPH PAL PLO PNB NR R8 TC DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t.

  (* [comment removed for export] *)
  Definition free_chitG_newfull_post (tk : ftail) (gn gf gl gqb nb fb lb qb bsz cnt maxc b : Z) (ks : list word) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word) (m' : word -> option byte),
    ms' = MS (mkR rac spd gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom rsegs)
    /\ munch (free_chitG_newfull_W tk spd thr p r8 n0 f0 lb b gl) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' lb [C8 (wz b); C8 (wz bsz); C8 (wz 1021)]
    /\ rw_cells rsegs m' (thr + 208 + 1920) [C4 (wz (cnt - 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)]
    /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv']
    /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (n + 8192)); C8 (wz 1); C8 (wz (p + -16))]
    /\ tail_post tk gn gf gl gqb (nb + 1) fb b (qb + (n + 8192)) thr m'.

  (* [comment removed for export] *)
  Ltac xferG H M WMH :=
    lazymatch type of M with munch ?W ?mi ?mc =>
    lazymatch type of H with
    | rw_cells _ _ ?A ?cs => apply (rw_cells_transport rsegs W mi mc A cs) in H; [| exact M| exact WMH|]
    | ro_cells _ _ ?A ?cs => apply (ro_cells_transport rsegs W mi mc A cs) in H; [| exact M|]
    end;
    [| cbn [disjoint_from app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add];
       OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
       first [ exact I | unfold QINST in *; slia ] ]
    end.

  (* [comment removed for export] *)
  Ltac split_ands H := lazymatch type of H with
    | _ /\ _ => let H1 := fresh "Q" in let H2 := fresh "Q" in destruct H as [H1 H2]; split_ands H1; split_ands H2 | _ => idtac end.
  Ltac osolve S M :=
    apply (munch_sets _ _ _ _ M); intros y Hy; unfold free_chitG_newfull_W, free_chit_newfull_W in Hy |- *; cbn [ctail_W] in Hy |- *;
    unfold free_cprefix_W, free_coreG_newfull_W, free_ccore_newfull_W, free_cdtail_W, free_cdtail_WA, QINST in Hy |- *;
    try rewrite S in Hy; try rewrite S; rewrite ?outside_app in Hy; rewrite ?outside_app; cbn [ctail_W app outside] in Hy |- *;
    split_ands Hy; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [assumption | exact I].

  #[using="DTAILA DTAIL0 PTAIL HEAD SEP_tc SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_pf SEP_pn SEP_pt SEP_pc KR KL STOR TRW STO DF0 DN0 DTOT DLEN DND DR FDR FRR TST TSDL CT8 TH0 TC PCo FCo SHC CTX0 HDR B1M B1R R8 NQ NR PHI PNB PLO PAL TPE RA2 SPH LO ST MI oldsh old tsd"] Theorem free_chitG_newfull : forall (tk : ftail) (gn gf gl gqb : Z) (glnx : word) (nb fb lb qb nx bsz cnt maxc sb : Z) (ks : list word) (kw statv bj0 bj1 bj2 bj3 : word),
    let b := sb + 24 * 2^32 + 16 * bv_unsigned kw in
    tail_pre tk gn gf gl gqb glnx m -> tail_ok tk gn gqb (qb + (n + 8192)) -> tail_apart tk gl thr p r8 n0 f0 [lb; b] ->
    nb <> 0 -> 0 <= nb < 2^63 -> 0 <= fb < 2^64 -> 0 <= qb -> thr mod 16 = 0 ->
    kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling ->
    apart lb 8192 thr 4096 -> apart lb 8192 (p + -16) (8 * r8 + 16) -> apart lb 8192 ctx 0x10000 ->
    apart lb 8192 n0 kDepotNodesBlock -> apart lb 8192 f0 kStackStoreBlockBytes ->
    1 <= cnt <= 16 -> length ks = 16%nat -> nth_error ks (Z.to_nat (cnt - 1)) = Some kw -> bv_unsigned kw < 2^32 ->
    0 <= sb -> sb + 2^37 <= 2^47 -> kHighMemBeg <= b -> b + 8192 <= alloc_ceiling ->
    apart b 8192 thr 4096 -> apart b 8192 (p + -16) (8 * r8 + 16) -> apart b 8192 ctx 0x10000 ->
    apart b 8192 n0 kDepotNodesBlock -> apart b 8192 f0 kStackStoreBlockBytes -> apart b 8192 lb 8192 ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] ->
    rw_cells rsegs m (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    rw_cells rsegs m (thr + 208 + 1920) [C4 (wz cnt); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (thr + 208 + 2576) [C8 statv] ->
    rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    evt rsegs (free_chitG_newfull_post tk gn gf gl gqb nb fb lb qb bsz cnt maxc b ks)
        (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz AINST) (wz p) a2 a3 (wz sto) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz dealloc_entry) fc None m (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros until bj3. cbv zeta. intros TPRE TOK TAP NB0 NBR FBR QB0 THRA LBL LBH Alt Alp Alc Aln Alf CNT LKS KW KWR SB0 SB1 BLO BHI Abt Abp Abc Abn Abf Abl SBC QC LB PC24 STA BC.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    remember (sb + 24 * 2^32 + 16 * bv_unsigned kw) as b eqn:BE.
    assert (QBN : qb + (n + 8192) < 2^64) by (destruct tk; cbn [tail_ok] in TOK; lia).
    (* [comment removed for export] *)
    pose proof (HEAD nb fb lb qb nx bsz cnt maxc sb ks kw statv bj0 bj1 bj2 bj3) as HD. cbv zeta in HD. rewrite <- BE in HD.
    eapply evt_cut; [exact (HD NB0 NBR QB0 QBN THRA LBL LBH Alt Alp Alc Aln Alf CNT LKS KW KWR SB0 SB1 BLO BHI Abt Abp Abc Abn Abf Abl SBC QC LB PC24 STA BC)|]. clear HD QC PC24 STA BC.
    intros ms' PO. unfold free_chead_newfull_post in PO. cbv zeta in PO. rewrite <- ?BE in PO.
    (first [ dex17 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7; dand16 PO as E MU7 WM7 MI7 ST7 PFR TST7 HDR7 CTX7 SHD7 DR7 QC7 LB7 PC7 STA7 B7 | dand33 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 E MU7 WM7 MI7 ST7 PFR TST7 HDR7 CTX7 SHD7 DR7 QC7 LB7 PC7 STA7 B7 | destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & m7 & E & MU7 & WM7 & MI7 & ST7 &
                    PFR & TST7 & HDR7 & CTX7 & SHD7 & DR7 & QC7 & LB7 & PC7 & STA7 & B7) ]). subst ms'.
    (* [comment removed for export] *)
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia). clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold free_chit_newfull_W, free_cprefix_W in MU7. rewrite SHF in MU7. cbn [app] in MU7.
    pose proof FCo as FC'. (first [ dand9 FC' as _ _ _ _ _ _ _ Fqmax _ | destruct FC' as (_ & _ & _ & _ & _ & _ & _ & Fqmax & _) ]). xferG Fqmax MU7 WM7.
    destruct tk; cbn [tail_pre tail_ok tail_apart] in TPRE, TOK, TAP.
    - (* [comment removed for export] *)
      eapply (PTAIL _ m7); [exact MI7| exact ST7| | faobj| exact PFR| exact QC7|].
      { lia. }
      intros ST8. apply evt_done. unfold free_chitG_newfull_post.
      hot_eexists_all. split; [reflexivity|].
      split. { osolve SHF MU7. }
      cbn [tail_post]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; kcell.
    - (* [comment removed for export] *)
      destruct TPRE as [LCK QGL]. xferG LCK MU7 WM7. xferG QGL MU7 WM7.
      eapply evt_cut; [eapply (DTAIL0 _ m m7 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (nb + 1) fb b (qb + (n + 8192)) 0 0 gf gqb gl);
                       first [exact MU7| exact WM7| eassumption| lia] |].
      intros ms' PO. cbv beta in PO. destruct_exs PO.
      (first [ dand15 PO as E MU WM MUt WMt MI9 ST9 TST9 HDR9 CTX9 SHD9 DR9 QC9 LCK9 QGL9 | destruct PO as (E & MU & WM & MUt & WMt & MI9 & ST9 & TST9 & HDR9 & CTX9 & SHD9 & DR9 & QC9 & LCK9 & QGL9) ]). subst ms'.
      rewrite ?unsigned_lit in MUt by lia. unfold free_cdtail_W, QINST in MUt.
      xfer LB7 MUt WMt. xfer PC7 MUt WMt. xfer STA7 MUt WMt. xfer B7 MUt WMt.
      apply evt_done. unfold free_chitG_newfull_post.
      hot_eexists_all. split; [reflexivity|].
      split. { osolve SHF MU. }
      cbn [tail_post]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; kcell.
    - (* [comment removed for export] *)
      (first [ dand3 TPRE as LCK QGL GLN | destruct TPRE as (LCK & QGL & GLN) ]). (first [ dand8 TAP as GL1 GL2 GL3 Agp Agt Agn Agf Agl | destruct TAP as (GL1 & GL2 & GL3 & Agp & Agt & Agn & Agf & Agl) ]). pose proof (Forall_inv (Forall_inv_tail Agl)) as Agb. apply Forall_inv in Agl.
      unfold apart, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in GL1, GL2, GL3, Agp, Agt, Agn, Agf, Agl, Agb.
      xferG LCK MU7 WM7. xferG QGL MU7 WM7. xferG GLN MU7 WM7.
      eapply evt_cut; [eapply (DTAILA _ m m7 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (nb + 1) fb b (qb + (n + 8192)) 0 0 gf gqb gn gl glnx);
                       first [exact MU7| exact WM7| eassumption| unfold apart, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes; lia] |].
      intros ms' PO. cbv beta in PO. destruct_exs PO.
      (first [ dand16 PO as E MU WM MUt WMt MI9 ST9 TST9 HDR9 CTX9 SHD9 DR9 QC9 LCK9 QGL9 GLN9 | destruct PO as (E & MU & WM & MUt & WMt & MI9 & ST9 & TST9 & HDR9 & CTX9 & SHD9 & DR9 & QC9 & LCK9 & QGL9 & GLN9) ]). subst ms'.
      rewrite ?unsigned_lit in MUt by lia. unfold free_cdtail_WA, QINST in MUt.
      xfer LB7 MUt WMt. xfer PC7 MUt WMt. xfer STA7 MUt WMt. xfer B7 MUt WMt.
      apply evt_done. unfold free_chitG_newfull_post.
      hot_eexists_all. split; [reflexivity|].
      split. { osolve SHF MU. }
      cbn [tail_post]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; kcell.
  Qed.
End FreeHitCore.
