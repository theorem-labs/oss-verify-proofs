(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt22wr AFreeH AFreeH0 AFreeHc AFreeH2c AFreeH3c ARtS4t2 AFreeC AFreeH4w AFreeH4r AFreeH4c AFreeH5e.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw.ARt23oh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw.ARt2hw4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt22wr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH2c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH3c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH5e.
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
Definition free_cpop_head_W (spd : word) (thr p r8 n0 f0 ri : Z) : list (Z * Z) :=
  free_cprefix_W spd thr p r8 n0 f0 ++ [(bv_unsigned spd + -80 - 224, bv_unsigned spd + -80); (ri + 128 * 24, ri + 128 * 24 + 8)].

(* [comment removed for export] *)
Definition free_cpop_head0_W (spd : word) (thr p r8 n0 f0 ri : Z) : list (Z * Z) :=
  free_cprefix_W spd thr p r8 n0 f0 ++ [(bv_unsigned spd + -80 - 224, bv_unsigned spd + -80); (thr + 208 + 80, thr + 208 + 2560); (ri + 128 * 24, ri + 128 * 24 + 8)].

Section FreeHitCore.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto : Z) (D : list (list Z)) (key : list Z) (old : word) (oldsh : list byte).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned spd).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned spd - 1024.   (* [comment removed for export] *)
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
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TST : rw_cells rsegs m (thr + 2824) [C8 (wz fr); C8 (wz fd)].
  Hypothesis FRR : 0 <= fr < 2^64.
  Hypothesis FDR : 0 <= fd < 2^64.
  (* [comment removed for export] *)
  Hypothesis DR : depot_repL AL_pasan rsegs D n0 f0 m.
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
  Let LO' : alloc_ceiling <= lo /\ lo <= bv_unsigned spd - 704. Proof. clear - LO. lia. Qed.
  Let PREFIX := free_cprefix rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto D key old oldsh MI ST LO' RA2 TPE PAL PLO PNB PHI NR NQ R8 B1R B1M HDR CTX0 SHC FCo PCo TC TH0 CT8 TSDL TST FRR FDR
    DR DND DLEN DTOT DN0 DF0 STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (sb ri : Z).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (thr + 208 + 80 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (free_array_of sb 24).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation uA := (bv_unsigned spd + -80 + 112).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (bv_unsigned spd + -80 + 112 + -128 + -48 + -32 + -128).
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_cpop_head_post (nb0 fb lb qb : Z) (ks : list word) (statv : word) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' : word) (scr pad rpad : list byte) (m' : word -> option byte),
      st = MS (mkR (wz refill_ret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) a0' (wz (thr + 208 + 2560)) (wz 24) (wz (E + 16)) (wz (Z.shiftr 2 1)) a5' a6' a7'
                   (wz (p + -16)) (wz 2305843009213693952) (wz fa) (wz 1099511627776) (wz 1152921504607895551)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
              F (wz gfa_locked) fc None m' (seg_rom rsegs)
      /\ munch (free_cpop_head_W spd thr p r8 n0 f0 ri) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (uA + -128 + -48 + -32 - 128)
      (* [comment removed for export] *)
      /\ rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]
      /\ rw_cells rsegs m' (usp + -80 + -64) (enqueue_frame pad (wz (p + -16)) (wz (thr + 208)) (wz sto) (wz n) (wz (thr + 80)) (wz QINST) (wz 0x3b72c))
      /\ rw_cells rsegs m' (usp + -80 + -64 + -32) (refill_frame rpad (wz (thr + 208)) (wz E) (wz enqueue_ret))
      /\ rw_cells rsegs m' uG (gfa_frame scr s11 s10 s9 s8 s7 (wz (2^20)) (wz n) (wz sto) (wz (thr + 80)) (wz (p + -16)) (wz 1) (wz E) (wz refill_ret))
      /\ rw_cells rsegs m' R [C8 (wz kMutexWriter)]
      (* [comment removed for export] *)
      /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
      /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
      /\ rw_cells rsegs m' p [C8 (wz fid)]
      /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
      /\ depot_repL AL_pasan rsegs D' n0 f0 m'
      /\ rw_cells rsegs m' (thr + 80) [C8 (wz nb0); C8 (wz fb); C8 (wz lb); C8 (wz qb)]
      /\ rw_cells rsegs m' E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)]
      /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv].

  #[using="SEP_rf SEP_rn SEP_rp SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBHI SBLO PREFIX LO' SEP_tc SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_pf SEP_pn SEP_pt SEP_pc KR KL STOR TRW STO DF0 DN0 DTOT DLEN DND DR FDR FRR TST TSDL CT8 TH0 TC PCo FCo SHC CTX0 HDR B1M B1R R8 NQ NR PHI PNB PLO PAL TPE RA2 SPH LO ST MI oldsh old ctx tsd"] Lemma free_cpop_head : forall (nb0 fb lb qb nx bsz : Z) (ks : list word) (statv : word),
    thr mod 16 = 0 -> length ks = 16%nat -> 0 <= nb0 < 2^63 ->
    (nb0 <> 0 -> kHighMemBeg <= lb /\ lb + 8192 <= alloc_ceiling /\ apart lb 8192 thr 4096 /\ apart lb 8192 (p + -16) (8 * r8 + 16)
               /\ apart lb 8192 n0 kDepotNodesBlock /\ apart lb 8192 f0 kStackStoreBlockBytes) ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m 0xb1d88 [C8 (wz ri)] ->
    rw_cells rsegs m (thr + 80) [C8 (wz nb0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (nb0 <> 0 -> rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)]) ->
    rw_cells rsegs m E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (thr + 208 + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] ->
    evt rsegs (free_cpop_head_post nb0 fb lb qb ks statv)
        (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz AINST) (wz p) a2 a3 (wz sto) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz dealloc_entry) fc None m (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros nb0 fb lb qb nx bsz ks statv THRA LKS NBR LBF SBC RIC QC LBC PC24 STA MXc.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *.
    apply PREFIX. intros t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' m6 PFR TST6 HDR6 CTX6 SHD6 DR6 MU6 WM6 MI6 ST6.
    unfold free_cprefix_W, off_th_unwinding, enqueue_entry in *. rewrite SHF in MU6.
    xfer SBC MU6 WM6. xfer RIC MU6 WM6. xfer QC MU6 WM6. xfer PC24 MU6 WM6. xfer STA MU6 WM6. xfer MXc MU6 WM6.
    assert (LBC6 : nb0 <> 0 -> rw_cells rsegs m6 lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)]).
    { intros NZ. specialize (LBC NZ). (first [ pose proof ((LBF NZ)) as dR_3; dand6 dR_3 as L1 L2 L3 L4 L5 L6 | destruct (LBF NZ) as (L1 & L2 & L3 & L4 & L5 & L6) ]). xfer LBC MU6 WM6. exact LBC. }
    clear LBC.
    pose proof (munch_refl [(usp + -80 - 224, usp + -80); (ri + 3072, ri + 3072 + 8)] m6) as MU. pose proof (wmono_refl rsegs m6) as WM.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (enq_pop_head _ (wz (usp + -80)) gp tp t0' t1' t2' _ _ a5' a6' a7' _ _ _ _ _ s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m6
                               lo thr sto (p + -16) n fb lb qb nx bsz sb ri ks); cbv zeta;
                     first [ eassumption | rewrite ?unsigned_lit by lia; first [eassumption | lia | kcellz]
                           | split; [faobj | lia]
                           | intros NZ; (first [ pose proof ((LBF NZ)) as dR_4; dand6 dR_4 as L1 L2 L3 L4 L5 L6 | destruct (LBF NZ) as (L1 & L2 & L3 & L4 & L5 & L6) ]); revert L1 L2 L3; clear; unfold kHighMemBeg, apart; intros; lia ] |].
    intros ms' PO. unfold enq_pop_head_post in PO. destruct_exs PO.
    (first [ dand9 PO as -> MUc WMc MI7 ST7 EF7 RF7 GF7 MX7 | destruct PO as (-> & MUc & WMc & MI7 & ST7 & EF7 & RF7 & GF7 & MX7) ]). rewrite ?unsigned_lit in MUc, ST7, EF7, RF7, GF7 by lia.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *.
    eapply bytes_at_transport in SHD6; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; unfold apart in SEP_rp; lia].
    clear SBC RIC MXc. xdepot DR6 MUc. box MU6. kpost MUc WMc. unfold boxed in MU6.
    rewrite ?unsigned_lit by lia.
    apply evt_done. unfold free_cpop_head_post, free_cpop_head_W, free_cprefix_W, off_th_unwinding, QINST. cbv zeta. rewrite SHF.
    change (80 * 24) with 1920. change (128 * 24) with 3072.
    hot_eexists_all. split; [reflexivity|].
    split. { lazymatch goal with MUg : munch _ m6 ?mb |- _ =>
               rewrite ?unsigned_lit in MUg by lia; cbn [app];
               eapply munch_trans; [eapply munch_weaken; [| exact MU6] | eapply munch_weaken; [| exact MUg]]; unfold sub_fp; cbn [outside]; intros y Hy; lia end. }
    split. { first [ exact WM6 | lazymatch goal with WMg : wmono rsegs m6 ?mb |- _ => exact (wmono_trans _ _ _ _ WM6 WMg) end ]. }
    unfold boxed in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [eassumption | kcellz].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_cpop_head0_post (nb0 fb lb qb : Z) (cnt : Z -> Z) (ksf : Z -> list word) (statv : word) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' : word) (scr pad rpad : list byte) (m' : word -> option byte),
      st = MS (mkR (wz refill_ret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) a0' (wz (thr + 208 + 2560)) (wz 24) (wz (E + 16)) (wz (Z.shiftr 2 1)) a5' a6' a7'
                   (wz (p + -16)) (wz 2305843009213693952) (wz fa) (wz 1099511627776) (wz 1152921504607895551)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
              F (wz gfa_locked) fc None m' (seg_rom rsegs)
      /\ munch (free_cpop_head0_W spd thr p r8 n0 f0 ri) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (uA + -128 + -48 + -32 - 128)
      /\ rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]
      /\ rw_cells rsegs m' (usp + -80 + -64) (enqueue_frame pad (wz (p + -16)) (wz (thr + 208)) (wz sto) (wz n) (wz (thr + 80)) (wz QINST) (wz 0x3b72c))
      /\ rw_cells rsegs m' (usp + -80 + -64 + -32) (refill_frame rpad (wz (thr + 208)) (wz E) (wz enqueue_ret))
      /\ rw_cells rsegs m' uG (gfa_frame scr s11 s10 s9 s8 s7 (wz (2^20)) (wz n) (wz sto) (wz (thr + 80)) (wz (p + -16)) (wz 1) (wz E) (wz refill_ret))
      /\ rw_cells rsegs m' R [C8 (wz kMutexWriter)]
      /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
      /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
      /\ rw_cells rsegs m' p [C8 (wz fid)]
      /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
      /\ depot_repL AL_pasan rsegs D' n0 f0 m'
      /\ rw_cells rsegs m' (thr + 80) [C8 (wz nb0); C8 (wz fb); C8 (wz lb); C8 (wz qb)]
      /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv]
      /\ (forall i, 1 <= i <= 31 ->
            rw_cells rsegs m' (thr + 208 + 80 * i) [C4 (wz (cnt i)); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s (ksf i))]).

  #[using="SEP_rf SEP_rn SEP_rp SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBHI SBLO PREFIX LO' SEP_tc SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_pf SEP_pn SEP_pt SEP_pc KR KL STOR TRW STO DF0 DN0 DTOT DLEN DND DR FDR FRR TST TSDL CT8 TH0 TC PCo FCo SHC CTX0 HDR B1M B1R R8 NQ NR PHI PNB PLO PAL TPE RA2 SPH LO ST MI oldsh old ctx tsd"] Lemma free_cpop_head0 : forall (nb0 fb lb qb nx bsz : Z) (cnt mc0 cs0 : Z -> Z) (ksf : Z -> list word) (statv : word),
    thr mod 16 = 0 -> 0 <= nb0 < 2^63 ->
    (nb0 <> 0 -> kHighMemBeg <= lb /\ lb + 8192 <= alloc_ceiling /\ apart lb 8192 thr 4096 /\ apart lb 8192 (p + -16) (8 * r8 + 16)
               /\ apart lb 8192 n0 kDepotNodesBlock /\ apart lb 8192 f0 kStackStoreBlockBytes) ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m 0xb1d88 [C8 (wz ri)] ->
    rw_cells rsegs m (thr + 80) [C8 (wz nb0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (nb0 <> 0 -> rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)]) ->
    (forall i, 1 <= i <= 31 -> 0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ksf i) = 16%nat /\
       rw_cells rsegs m (thr + 208 + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (ksf i))]) ->
    cnt 24 = 0 -> mc0 24 = 0 ->
    rw_cells rsegs m (thr + 208 + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] ->
    evt rsegs (free_cpop_head0_post nb0 fb lb qb cnt ksf statv)
        (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz AINST) (wz p) a2 a3 (wz sto) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz dealloc_entry) fc None m (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros nb0 fb lb qb nx bsz cnt mc0 cs0 ksf statv THRA NBR LBF SBC RIC QC LBC LINES CNT0 MC0 STA MXc.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *.
    apply PREFIX. intros t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' m6 PFR TST6 HDR6 CTX6 SHD6 DR6 MU6 WM6 MI6 ST6.
    unfold free_cprefix_W, off_th_unwinding, enqueue_entry in *. rewrite SHF in MU6.
    xfer SBC MU6 WM6. xfer RIC MU6 WM6. xfer QC MU6 WM6. xfer STA MU6 WM6. xfer MXc MU6 WM6.
    assert (LBC6 : nb0 <> 0 -> rw_cells rsegs m6 lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)]).
    { intros NZ. specialize (LBC NZ). (first [ pose proof ((LBF NZ)) as dR_8; dand6 dR_8 as L1 L2 L3 L4 L5 L6 | destruct (LBF NZ) as (L1 & L2 & L3 & L4 & L5 & L6) ]). xfer LBC MU6 WM6. exact LBC. }
    clear LBC.
    assert (LINES6 : forall i, 1 <= i <= 31 -> 0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ksf i) = 16%nat /\
              rw_cells rsegs m6 (thr + 208 + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (ksf i))]).
    { intros i Hi; (first [ pose proof ((LINES i Hi)) as dR_9; dand5 dR_9 as X1 X2 X3 X4 X5 | destruct (LINES i Hi) as (X1 & X2 & X3 & X4 & X5) ]); refine (conj X1 (conj X2 (conj X3 (conj X4 _)))).
      eapply (rw_cells_transport rsegs _ m m6); [exact X5 | exact MU6 | exact WM6 | cbn [disjoint_from]; simpl_sizes; slia]. }
    clear LINES.
    pose proof (munch_refl [(usp + -80 - 224, usp + -80); (thr + 208 + 80, thr + 208 + 2560); (ri + 3072, ri + 3072 + 8)] m6) as MU. pose proof (wmono_refl rsegs m6) as WM.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (enq_pop_head0 _ (wz (usp + -80)) gp tp t0' t1' t2' _ _ a5' a6' a7' _ _ _ _ _ s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m6
                               lo thr sto (p + -16) n fb lb qb nx bsz sb ri (ksf 24)); cbv zeta;
                     first [ eassumption | rewrite ?unsigned_lit by lia; first [eassumption | lia | kcellz]
                           | split; [faobj | lia]
                           | exact (proj1 (proj2 (proj2 (proj2 (LINES6 24 ltac:(lia))))))
                           | intros NZ; (first [ pose proof ((LBF NZ)) as dR_10; dand6 dR_10 as L1 L2 L3 L4 L5 L6 | destruct (LBF NZ) as (L1 & L2 & L3 & L4 & L5 & L6) ]); revert L1 L2 L3; clear; unfold kHighMemBeg, apart; intros; lia ] |].
    intros ms' PO. unfold enq_pop_head0_post in PO. destruct_exs PO.
    (first [ dand10 PO as -> MUc WMc MI7 ST7 EF7 RF7 GF7 MX7 LINES7 | destruct PO as (-> & MUc & WMc & MI7 & ST7 & EF7 & RF7 & GF7 & MX7 & LINES7) ]). rewrite ?unsigned_lit in MUc, ST7, EF7, RF7, GF7 by lia.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *.
    eapply bytes_at_transport in SHD6; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; unfold apart in SEP_rp, SEP_pt; lia].
    clear SBC RIC MXc LINES6. xdepot DR6 MUc. box MU6. kpost MUc WMc. unfold boxed in MU6.
    rewrite ?unsigned_lit by lia.
    apply evt_done. unfold free_cpop_head0_post, free_cpop_head0_W, free_cprefix_W, off_th_unwinding, QINST. cbv zeta. rewrite SHF.
    change (80 * 24) with 1920. change (128 * 24) with 3072.
    hot_eexists_all. split; [reflexivity|].
    split. { lazymatch goal with MUg : munch _ m6 ?mb |- _ =>
               rewrite ?unsigned_lit in MUg by lia; cbn [app];
               eapply munch_trans; [eapply munch_weaken; [| exact MU6] | eapply munch_weaken; [| exact MUg]]; unfold sub_fp; cbn [outside]; intros y Hy; lia end. }
    split. { first [ exact WM6 | lazymatch goal with WMg : wmono rsegs m6 ?mb |- _ => exact (wmono_trans _ _ _ _ WM6 WMg) end ]. }
    unfold boxed in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [eassumption | kcellz].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Tail.
  Variables (a0g t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (scr pad rpad : list byte) (statv0 na w bj0 bj1 bj2 bj3 : word)
            (nf' fb lb qb : Z) (ks : list word) (mg : word -> option byte).
  #[warnings="-notation-for-abbreviation"] Local Notation b := (sb + 24 * 2^32 + 16 * bv_unsigned w).
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis NFR : 1 <= nf' < 2^27.
  Hypothesis WR : bv_unsigned w < 2^32.
  Hypothesis BLO : kHighMemBeg <= b.
  Hypothesis BHI : b + 8192 <= alloc_ceiling.
  Hypothesis BFA : b + 8192 <= fa.
  Hypothesis Abt : apart b 8192 thr 4096.
  Hypothesis Abp : apart b 8192 (p + -16) (8 * r8 + 16).
  Hypothesis Abn : apart b 8192 n0 kDepotNodesBlock.
  Hypothesis Abf : apart b 8192 f0 kStackStoreBlockBytes.
  Hypothesis Abr : apart b 8192 ri 4096.
  Hypothesis MIg : mem_inv rsegs mg.
  Hypothesis STg : stk rsegs mg lo uG.
  (* [comment removed for export] *)
  Hypothesis PFRg : rw_cells rsegs mg (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac].
  Hypothesis EFg : rw_cells rsegs mg (usp + -80 + -64) (enqueue_frame pad (wz (p + -16)) (wz (thr + 208)) (wz sto) (wz n) (wz (thr + 80)) (wz QINST) (wz 0x3b72c)).
  Hypothesis RFg : rw_cells rsegs mg (usp + -80 + -64 + -32) (refill_frame rpad (wz (thr + 208)) (wz E) (wz enqueue_ret)).
  Hypothesis GFg : rw_cells rsegs mg uG (gfa_frame scr s11 s10 s9 s8 s7 (wz (2^20)) (wz n) (wz sto) (wz (thr + 80)) (wz (p + -16)) (wz 1) (wz E) (wz refill_ret)).
  (* [comment removed for export] *)
  Hypothesis TSTg : rw_cells rsegs mg (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))].
  Hypothesis HDRg : rw_cells rsegs mg (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)].
  Hypothesis CTXg : rw_cells rsegs mg p [C8 (wz fid)].
  Hypothesis SHDg : bytes_at rsegs mg (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)).
  Hypothesis DRg : depot_repL AL_pasan rsegs D' n0 f0 mg.
  (* [comment removed for export] *)
  Hypothesis CSBg : ro_cells rsegs mg 0xb1d78 [C8 (wz sb)].
  Hypothesis MXg : rw_cells rsegs mg R [C8 (wz kMutexWriter)].
  Hypothesis NFCg : rw_cells rsegs mg (R + 16) [C8 (wz nf')].
  Hypothesis NALg : rw_cells rsegs mg (R + 72) [C8 na].
  Hypothesis FARRg : u32arr rsegs mg (fa + 4 * (nf' - 1)) [w].
  Hypothesis PCg : rw_cells rsegs mg E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)].
  Hypothesis STAg : rw_cells rsegs mg (thr + 208 + 2576) [C8 statv0].
  Hypothesis BCg : rw_cells rsegs mg b [C8 bj0; C8 bj1; C8 bj2; C8 bj3].

  Local Ltac tail_prep CV SHF :=
    pose proof (zr_word spd) as SPR; unfold inr64 in SPR;
    pose proof TC as TC'; destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds);
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]); free_lin.

  (* [comment removed for export] *)
  #[using="BCg STAg PCg FARRg NALg NFCg MXg CSBg DRg SHDg CTXg HDRg TSTg GFg RFg EFg PFRg STg MIg Abr Abf Abn Abp Abt BFA BHI BLO WR NFR LKS THRA bj3 bj2 bj1 bj0 statv0 rpad pad scr SEP_rf SEP_rn SEP_rp SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBAL SBHI SBLO LO' fid D' SEP_f0t SEP_n0t SEP_pt KL STOR DF0 DN0 TC R8 NR PNB PLO PAL SPH SPA LO ctx tsd m Clg"] Lemma free_cpop_tail0 :
    rw_cells rsegs mg (thr + 80) [C8 (wz 0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    evt rsegs (free_cenq_new0F_post rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p n b1 thr r8 n0 f0 fr fd sto D key sb ri nf' w na fb lb qb ks mg)
        (MS (mkR (wz gfa_popret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) (wz 1) a1' a2' a3' a4' a5' a6' a7'
                 a0g (wz 2305843009213693952) (wz fa) (wz (E + 16)) (wz (Z.shiftr 2 1)) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
            F (ret_pc (wz gfa_popret)) fc None mg (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros QCg.
    pose proof alloc_ceiling_val as CV. tail_prep CV CV.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold off_th_unwinding, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *. rewrite SHF in SHDg.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *.
    box LKS || idtac.
    pose proof (munch_refl (free_ccore_new0F_W spd thr b ri) mg) as MU. unfold free_ccore_new0F_W in MU. pose proof (wmono_refl rsegs mg) as WM.
    (* [comment removed for export] *)
    replace (usp + -80 + 112 + -128 + -48 + -32 + -128) with (bv_unsigned (Z_to_bv 64 (usp + -80)) + 112 + -128 + -48 + -32 + -128) by (rewrite unsigned_lit by lia; reflexivity).
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (enq_pop_tail0 (wz 0x3b72c) (wz (usp + -80)) gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F fc
                               lo thr sto (p + -16) n fb lb qb sb ri ks); cbv zeta;
                     first [ eassumption | unfold boxed in *; assumption
                           | rewrite ?unsigned_lit by lia; first [eassumption | lia | kcellz | zmod]
                           | split; [faobj | lia]
                           | lazymatch goal with |- apart _ _ _ _ => first [ revert Abt; unfold apart; clear; intros; lia | revert Abr; unfold apart; clear; intros; lia ] end ] |].
    intros ms' PO. unfold enq_refill_post0, enq_refill_W0 in PO. cbv zeta in PO. destruct_exs PO.
    (first [ dand13 PO as -> MUc WMc MI7 ST7 QC7 PC7 STA7 BC7 MX7 NFC7 NAL7 FARR7 | destruct PO as (-> & MUc & WMc & MI7 & ST7 & QC7 & PC7 & STA7 & BC7 & MX7 & NFC7 & NAL7 & FARR7) ]).
    rewrite ?unsigned_lit in MUc, ST7 by lia.
    eapply bytes_at_transport in SHDg; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; unfold apart in Abp, SEP_rp; lia].
    clear CSBg QCg PCg STAg BCg MXg NFCg NALg FARRg GFg RFg EFg. xdepot DRg MUc. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x3b72c)) with (Z_to_bv 64 0x3b72c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply evt_done. unfold free_cenq_new0F_post, free_ccore_new0F_W, off_th_unwinding, QINST. cbv zeta. rewrite SHF.
    hot_eexists_all. split; [reflexivity|].
    unfold boxed in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [eassumption | kcellz].
  Qed.

  (* [comment removed for export] *)
  #[using="BCg STAg PCg FARRg NALg NFCg MXg CSBg DRg SHDg CTXg HDRg TSTg GFg RFg EFg PFRg STg MIg Abr Abf Abn Abp Abt BFA BHI BLO WR NFR LKS THRA bj3 bj2 bj1 bj0 statv0 rpad pad scr SEP_rf SEP_rn SEP_rp SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBAL SBHI SBLO LO' fid D' SEP_f0t SEP_n0t SEP_pt KL STOR DF0 DN0 TC R8 NR PNB PLO PAL SPH SPA LO tsd m"] Lemma free_cpop_tailF : forall (nb nx bsz : Z),
    nb <> 0 -> 0 <= nb < 2^63 ->
    kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling -> lb + 8192 <= fa ->
    apart lb 8192 thr 4096 -> apart lb 8192 (p + -16) (8 * r8 + 16) -> apart lb 8192 ctx 0x10000 ->
    apart lb 8192 n0 kDepotNodesBlock -> apart lb 8192 f0 kStackStoreBlockBytes -> apart lb 8192 ri 4096 -> apart b 8192 lb 8192 ->
    rw_cells rsegs mg (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs mg lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    evt rsegs (free_cenq_newfullF_post rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p n b1 thr r8 n0 f0 fr fd sto D key sb ri nf' w na nb fb lb qb bsz ks mg)
        (MS (mkR (wz gfa_popret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) (wz 1) a1' a2' a3' a4' a5' a6' a7'
                 a0g (wz 2305843009213693952) (wz fa) (wz (E + 16)) (wz (Z.shiftr 2 1)) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
            F (ret_pc (wz gfa_popret)) fc None mg (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros nb nx bsz NB NBR LBLO LBHI LBFA Albt Albp Albc Albn Albf Albr Ablb QCg LBCg.
    pose proof alloc_ceiling_val as CV. tail_prep CV CV.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold off_th_unwinding, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *. rewrite SHF in SHDg.
    change (80 * 24) with 1920 in *. change (128 * 24) with 3072 in *.
    box LKS || idtac.
    pose proof (munch_refl (free_ccore_newfullF_W spd thr b ri lb) mg) as MU. unfold free_ccore_newfullF_W in MU. pose proof (wmono_refl rsegs mg) as WM.
    replace (usp + -80 + 112 + -128 + -48 + -32 + -128) with (bv_unsigned (Z_to_bv 64 (usp + -80)) + 112 + -128 + -48 + -32 + -128) by (rewrite unsigned_lit by lia; reflexivity).
    eapply evt_cut; [eapply (enq_pop_tailF (wz 0x3b72c) (wz (usp + -80)) gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F fc
                               lo thr sto (p + -16) n fb lb qb nx bsz sb ri ks); cbv zeta;
                     first [ eassumption | unfold boxed in *; assumption
                           | rewrite ?unsigned_lit by lia; first [eassumption | lia | kcellz | zmod]
                           | split; [faobj | lia]
                           | lazymatch goal with |- apart _ _ _ _ =>
                               first [ revert Abt; unfold apart; clear; intros; lia | revert Abr; unfold apart; clear; intros; lia
                                     | revert Albt; unfold apart; clear; intros; lia | revert Albr; unfold apart; clear; intros; lia
                                     | revert Ablb; unfold apart; clear; intros; lia ] end ] |].
    intros ms' PO. unfold enq_refill_postF, enq_refill_WF in PO. cbv zeta in PO. destruct_exs PO.
    (first [ dand14 PO as -> MUc WMc MI7 ST7 QC7 LBC7 PC7 STA7 BC7 MX7 NFC7 NAL7 FARR7 | destruct PO as (-> & MUc & WMc & MI7 & ST7 & QC7 & LBC7 & PC7 & STA7 & BC7 & MX7 & NFC7 & NAL7 & FARR7) ]).
    rewrite ?unsigned_lit in MUc, ST7 by lia.
    eapply bytes_at_transport in SHDg; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; unfold apart in Abp, SEP_rp, Albp; lia].
    clear CSBg QCg LBCg PCg STAg BCg MXg NFCg NALg FARRg GFg RFg EFg. xdepot DRg MUc. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x3b72c)) with (Z_to_bv 64 0x3b72c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply evt_done. unfold free_cenq_newfullF_post, free_ccore_newfullF_W, off_th_unwinding, QINST. cbv zeta. rewrite SHF.
    hot_eexists_all. split; [reflexivity|].
    unfold boxed in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [eassumption | kcellz].
  Qed.
  End Tail.
End FreeHitCore.
