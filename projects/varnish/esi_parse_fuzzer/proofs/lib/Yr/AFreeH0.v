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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 AMTac ARt2_lib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt2gfb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt22wr ARt22fz AIcpnnp AFreeH.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt20wx.ARt27j4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2gfb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw.ARt23oh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw.ARt2hw4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt22wr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt22fz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietcz7.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_cfree_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietcz7.dl_tf_cfree_lia.
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

Definition free_prefix0_W (sp : word) (lo thr p r8 n0 f0 : Z) : list (Z * Z) :=
  free_prefix_W sp lo thr p r8 n0 f0 ++
  [(0x144e48, 0x144e4c); (IAB, IAB + 1); (IAB + 8, IAB + 8 + 262144); (IAB + 0x40040, IAB + 0x40040 + 3456);
   (IAB + 0x40dc0, IAB + 0x40dc0 + 262728); (IAB + 0x81008, IAB + 0x81008 + 40)].

(* [comment removed for export] *)
Lemma zeros_word_at : forall (m : word -> option byte) A n k,
  rw_cells rsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] -> 0 <= k -> k + 8 <= n ->
  ro_cells rsegs m (A + k) [C8 (wz 0)].
Proof.
  intros m A n k [[_ B] _] K0 K8. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. (first [ dand3 B as B0 B1 B | destruct B as (B0 & B1 & B) ]).
  rewrite repeat_length in B1, B.
  apply ro_C8_of_bytes. rewrite le8_zero_repeat. split; [lia|]. split; [rewrite repeat_length; cbn; lia|].
  intros i Hi. rewrite repeat_length in Hi.
  replace (A + k + Z.of_nat i) with (A + Z.of_nat (Z.to_nat k + i)) by lia.
  rewrite (B (Z.to_nat k + i)%nat ltac:(lia)). rewrite !nth_error_repeat by lia. reflexivity.
Qed.

Lemma outside_app : forall A B x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof. induction A as [|[u v] A IH]; intros B x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)
Ltac xferbig H M WMH :=
  lazymatch type of M with munch ?W ?mi ?mc =>
  lazymatch type of H with
  | rw_cells _ _ ?A ?cs => apply (rw_cells_transport rsegs W mi mc A cs) in H; [| exact M| exact WMH| cbn [disjoint_from cells_size csize Nat.add]; rewrite ?repeat_length; lia]
  | u64arr _ _ ?A ?xs => apply (u64arr_transport rsegs W mi mc A xs) in H; [| exact M| exact WMH| cbn [disjoint_from]; first [rewrite repeat_length | match goal with L : length xs = _ |- _ => rewrite L end]; lia]
  end end.
Ltac xferb H M WMH := first [ xferbig H M WMH | xfer H M WMH ].
Definition keep (P : Prop) : Prop := P.
(* [comment removed for export] *)
Ltac kcell :=
  lazymatch goal with
  | |- rw_cells _ ?mm ?A _ => match goal with H : rw_cells _ mm A _ |- _ => exact H end
  | |- ro_cells _ ?mm ?A _ => match goal with H : ro_cells _ mm A _ |- _ => exact H end
  | |- bytes_at _ ?mm ?A _ => match goal with H : bytes_at _ mm A _ |- _ => exact H end
  | |- u64arr _ ?mm ?A _ => match goal with H : u64arr _ mm A _ |- _ => exact H end
  | |- _ => eassumption
  end.
Ltac kp H := lazymatch type of H with ?t => change t with (keep t) in H end.

(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.

Section FreeHit.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p n b1 tsd ctx thr top bot r8 n0 f0 fr fd : Z) (D : list (list Z)) (old : word) (oldsh : list byte).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 2688.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RANE : bv_unsigned ra <> 0x58ab4.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis VLE : bv_unsigned s0 <= bv_unsigned sp.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
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
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (wz ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (wz kMainTid)].
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)].
  Hypothesis TDT : ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis TST : rw_cells rsegs m (thr + 2824) [C8 (wz fr); C8 (wz fd)].
  Hypothesis FRR : 0 <= fr < 2^64.
  Hypothesis FDR : 0 <= fd < 2^64.
  (* [comment removed for export] *)
  Hypothesis DR : depot_repL AL_pasan rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 3 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
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

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).
  Let KEY : list Z := free_key top bot fp ra.
  Let D' : list (list Z) := fst (depot_putC D KEY).
  Let fid : Z := snd (depot_putC D KEY).

  (* [comment removed for export] *)

End FreeHit.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
