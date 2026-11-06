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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtSnjd AMTac ARt2_lib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeH AFreeH0 AFreeT AFreeHc AFreeDc AFreeH2c ARtS4t2 AFreeH4w AFreeH4r AFreeH4c AFrea6l.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt23nw.ARt23oh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeDc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH2c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFrea6l.
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
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LKS; @RILO; @PNB; @SBLO; @LBthr; @SPR; @TOK; @LO; @Agt; @NBR; @GL3; @NB0; @BLO; @LBL; @CV; @NFR; @PQ; @ADN0; @ADF0; @RIHI; @SEP_tr; @Aglr; @BHI; @QBN; @LBH; @Alt; @Abt; @SBHI; @SEP_ts; @NR; @R8; @Agp; @GL1; @Agl; @Agb; @GL2; @Agn; @Agf; @LPLO; @Aglfa])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
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
Definition free_coreR_newfullF_W (thr lb b ri : Z) : list (Z * Z) :=
  [(thr + 80, thr + 112); (lb, lb + 8); (thr + 208 + 1920, thr + 208 + 2000); (thr + 208 + 2576, thr + 208 + 2584); (b, b + 32);
   (ri + 3072, ri + 3080); (ri + 3088, ri + 3096); (ri + 3144, ri + 3152)].
Definition free_chitR_newfullF_W (tk : ftail) (spd : word) (thr p r8 n0 f0 lb b gl ri : Z) : list (Z * Z) :=
  free_cprefix_W spd thr p r8 n0 f0 ++ free_coreR_newfullF_W thr lb b ri ++ ctail_W tk spd thr gl.

Lemma munch_setsF3 : forall W W' (ma mb : mem), munch W ma mb -> (forall x, outside W' x -> outside W x) -> munch W' ma mb.
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
  Hypothesis Afap : apart (sb + 24 * 2^32 + 3758096384) (4 * 2^27) (p + -16) (8 * r8 + 16).
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

  Let HEAD := free_chead_newfullF rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto D key old oldsh MI ST LO SPA SPH RA2 TPE PAL PLO PNB PHI NR NQ R8 B1R B1M HDR CTX0 SHC FCo PCo TC TH0 CT8 TSDL TST FRR FDR
    DR DND DLEN DTOT DN0 DF0 STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc
    sb ri nf w na SBLO SBHI SBAL RILO RIHI RIAL SEP_tr SEP_ts SEP_rs SEP_rp SEP_rn SEP_rf SEP_ns SEP_fs Afap WR NFR BLO BHI BFA Abt Abp Abn Abf.
  Let DTAIL0 := free_cdtailR0 rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto D key
    LO SPH PAL PLO PNB NR R8 TC DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t.
  Let DTAILA := free_cdtailRA rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto D key
    LO SPH PAL PLO PNB NR R8 TC DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t.

  (* [comment removed for export] *)
  Definition free_chitR_newfullF_post (tk : ftail) (gn gf gl gqb nb fb lb qb bsz qmin : Z) (ks : list word) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word) (m' : word -> option byte),
    ms' = MS (mkR (wz 0x3b664) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                 (wz QINST) (wz qmin) (wz (thr + 208)) (wz sto) a4' a5' a6' a7'
                 (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz recycle_entry) fc None m' (seg_rom rsegs)
    /\ munch (free_chitR_newfullF_W tk spd thr p r8 n0 f0 lb b gl ri) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (usp + -80)
    /\ rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pasan rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' lb [C8 (wz b); C8 (wz bsz); C8 (wz 1021)]
    /\ rw_cells rsegs m' (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ([w] ++ skipn 1 ks))]
    /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv']
    /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (n + 8192)); C8 (wz 1); C8 (wz (p + -16))]
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf - 1))]
    /\ rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + 1))]
    /\ u32arr rsegs m' (fa + 4 * (nf - 1)) [w]
    /\ tail_postR tk gn gf gl gqb (nb + 1) fb b (qb + (n + 8192)) qmin thr m'.

  (* [comment removed for export] *)
  Ltac xferG H M WMH :=
    lazymatch type of M with munch ?W ?mi ?mc =>
    lazymatch type of H with
    | rw_cells _ _ ?A ?cs => apply (rw_cells_transport rsegs W mi mc A cs) in H; [| exact M| exact WMH|]
    | ro_cells _ _ ?A ?cs => apply (ro_cells_transport rsegs W mi mc A cs) in H; [| exact M|]
    | u32arr _ _ ?A ?xs => apply (u32arr_transport rsegs W mi mc A xs) in H; [| exact M| exact WMH|]; try (simpl_arr_sizes)
    end;
    [| cbn [disjoint_from app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add];
       OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
       first [ exact I | unfold QINST in *; slia ] ]
    end.

  (* [comment removed for export] *)
  Ltac split_ands H := lazymatch type of H with
    | _ /\ _ => let H1 := fresh "Q" in let H2 := fresh "Q" in destruct H as [H1 H2]; split_ands H1; split_ands H2 | _ => idtac end.
  Ltac osolve S M :=
    apply (munch_setsF3 _ _ _ _ M); intros y Hy; unfold free_chitR_newfullF_W, free_chit_newfullF_W in Hy |- *; cbn [ctail_W] in Hy |- *;
    unfold free_cprefix_W, free_coreR_newfullF_W, free_ccore_newfullF_W, free_cdtailR_W, free_cdtailR_WA, free_cdtail_W, free_cdtail_WA, QINST in Hy |- *;
    try rewrite S in Hy; try rewrite S; rewrite ?outside_app in Hy; rewrite ?outside_app; cbn [ctail_W app outside] in Hy |- *;
    split_ands Hy; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [assumption | exact I].

  (* [comment removed for export] *)
  #[using="DTAILA DTAIL0 Abt BHI BLO NFR SEP_ts SEP_tr RIHI RILO SBHI SBLO SEP_f0t SEP_n0t SEP_pt KL STOR DF0 DN0 TC FCo R8 NR PNB PLO PAL SPH LO tsd"] Theorem free_chitR_newfullF_tl : forall (tk : ftail) (gn gf gl gqb : Z) (glnx : word) (nb fb lb qb nx bsz : Z) (ks : list word) (statv bj0 bj1 bj2 bj3 : word) (qmin : Z) (ms7 : machine_state),
    tail_pre tk gn gf gl gqb glnx m -> tail_okR tk gn gqb (qb + (n + 8192)) -> tail_apart tk gl thr p r8 n0 f0 [lb; b] ->
    0 <= qmin < 2^64 -> ro_cells rsegs m (QINST + 64) [C8 (wz (2^28)); C8 (wz qmin)] ->
    (tk = TA -> apart gl 24 ri 4096 /\ apart gl 24 (sb + 24 * 2^32 + 3758096384) (4 * 2^27)) ->
    nb <> 0 -> 0 <= nb < 2^40 -> 0 <= fb < 2^64 -> 0 <= qb -> thr mod 16 = 0 -> length ks = 16%nat ->
    kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling -> lb + 8192 <= fa ->
    apart lb 8192 thr 4096 -> apart lb 8192 (p + -16) (8 * r8 + 16) -> apart lb 8192 ctx 0x10000 ->
    apart lb 8192 n0 kDepotNodesBlock -> apart lb 8192 f0 kStackStoreBlockBytes -> apart lb 8192 ri 4096 -> apart b 8192 lb 8192 ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m 0xb1d88 [C8 (wz ri)] ->
    rw_cells rsegs m (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    rw_cells rsegs m (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (thr + 208 + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] -> rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 72) [C8 na] ->
    u32arr rsegs m (fa + 4 * (nf - 1)) [w] ->
    rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    free_chead_newfullF_post rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p n b1 thr r8 n0 f0 fr fd sto D key sb ri nf w na nb fb lb qb bsz ks ms7 ->
    evt rsegs (free_chitR_newfullF_post tk gn gf gl gqb nb fb lb qb bsz qmin ks) ms7.
  Proof. natz_kl_box.
    intros until ms7. intros TPRE TOK TAP QMR QMM TAPR NB0 NBR FBR QB0 THRA LKS LBL LBH LBFA Alt Alp Alc Aln Alf Alr Abl SBC RIC QC LB PC24 STA MXc NFCc NALc FARRc BC PO.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    assert (QBN : qb + (n + 8192) < 2^64) by (destruct tk; cbn [tail_okR] in TOK; [destruct TOK| |]; lia).
    (* [comment removed for export] *)
    clear QC LB PC24 STA BC MXc NFCc NALc FARRc.
    rename ms7 into ms'. unfold free_chead_newfullF_post in PO. cbv zeta in PO.
    (first [ dex17 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7; dand20 PO as E MU7 WM7 MI7 ST7 PFR TST7 HDR7 CTX7 SHD7 DR7 QC7 LB7 PC7 STA7 B7 MX7 NFC7 NAL7 FARR7 | dand36 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 E MU7 WM7 MI7 ST7 PFR TST7 HDR7 CTX7 SHD7 DR7 QC7 LB7 PC7 STA7 B7 MX7 NFC7 dR_PO_t0; destruct dR_PO_t0 as [NAL7 FARR7] | destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & m7 & E & MU7 & WM7 & MI7 & ST7 &
                    PFR & TST7 & HDR7 & CTX7 & SHD7 & DR7 & QC7 & LB7 & PC7 & STA7 & B7 & MX7 & NFC7 & NAL7 & FARR7) ]). subst ms'.
    (* [comment removed for export] *)
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia). clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold free_chit_newfullF_W, free_cprefix_W in MU7. rewrite SHF in MU7. cbn [app] in MU7.
    pose proof FCo as FC'. (first [ dand9 FC' as _ _ _ _ _ _ _ Fqmax _ | destruct FC' as (_ & _ & _ & _ & _ & _ & _ & Fqmax & _) ]). xferG Fqmax MU7 WM7. xferG QMM MU7 WM7.
    destruct tk; cbn [tail_pre tail_okR tail_apart] in TPRE, TOK, TAP; [destruct TOK| |].
    - (* [comment removed for export] *)
      destruct TPRE as [LCK QGL]. xferG LCK MU7 WM7. xferG QGL MU7 WM7.
      eapply (DTAIL0 _ m m7 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (nb + 1) fb b (qb + (n + 8192)) 0 0 gf gqb gl qmin);
        first [exact MU7| exact WM7| eassumption| lia| reflexivity| idtac].
      intros t0'' t1'' a4'' a5'' a6'' a7'' m' PFR' TST9 HDR9 CTX9 SHD9 DR9 QC9 LCK9 QGL9 QMM9 MU WM MUt WMt MI9 ST9.
      rewrite ?unsigned_lit in MUt by lia. unfold free_cdtailR_W, free_cdtail_W, QINST in MUt.
      xfer LB7 MUt WMt. xfer PC7 MUt WMt. xfer STA7 MUt WMt. xfer B7 MUt WMt. xfer MX7 MUt WMt. xfer NFC7 MUt WMt. xfer NAL7 MUt WMt.
      unfold free_array_of in FARR7.
      lazymatch type of MUt with munch ?W ?mi ?mc =>
        apply (u32arr_transport rsegs W mi mc) in FARR7; [| exact MUt| exact WMt| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia] end.
      apply evt_done. unfold free_chitR_newfullF_post.
      hot_eexists_all. split; [reflexivity|].
      split. { osolve SHF MU. }
      cbn [tail_postR]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; kcell.
    - (* [comment removed for export] *)
      (first [ dand3 TPRE as LCK QGL GLN | destruct TPRE as (LCK & QGL & GLN) ]). (first [ dand8 TAP as GL1 GL2 GL3 Agp Agt Agn Agf Agl | destruct TAP as (GL1 & GL2 & GL3 & Agp & Agt & Agn & Agf & Agl) ]). pose proof (Forall_inv (Forall_inv_tail Agl)) as Agb. apply Forall_inv in Agl.
      destruct (TAPR eq_refl) as [Aglr Aglfa].
      unfold apart, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in GL1, GL2, GL3, Agp, Agt, Agn, Agf, Agl, Agb.
      xferG LCK MU7 WM7. xferG QGL MU7 WM7. xferG GLN MU7 WM7.
      eapply (DTAILA _ m m7 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (nb + 1) fb b (qb + (n + 8192)) 0 0 gf gqb gn gl glnx qmin);
        first [exact MU7| exact WM7| eassumption| unfold apart, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes; lia| reflexivity| idtac].
      intros t0'' t1'' a4'' a5'' a6'' a7'' m' PFR' TST9 HDR9 CTX9 SHD9 DR9 QC9 LCK9 QGL9 GLN9 QMM9 MU WM MUt WMt MI9 ST9.
      rewrite ?unsigned_lit in MUt by lia. unfold free_cdtailR_WA, free_cdtail_WA, QINST in MUt.
      xfer LB7 MUt WMt. xfer PC7 MUt WMt. xfer STA7 MUt WMt. xfer B7 MUt WMt. xfer MX7 MUt WMt. xfer NFC7 MUt WMt. xfer NAL7 MUt WMt.
      unfold free_array_of in FARR7.
      lazymatch type of MUt with munch ?W ?mi ?mc =>
        apply (u32arr_transport rsegs W mi mc) in FARR7; [| exact MUt| exact WMt| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia] end.
      apply evt_done. unfold free_chitR_newfullF_post.
      hot_eexists_all. split; [reflexivity|].
      split. { osolve SHF MU. }
      cbn [tail_postR]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; kcell.
  Qed.

  #[using="DTAILA DTAIL0 HEAD Abf Abn Abp Abt BFA BHI BLO NFR WR Afap SEP_fs SEP_ns SEP_rf SEP_rn SEP_rp SEP_rs SEP_ts SEP_tr RIAL RIHI RILO SBAL SBHI SBLO SEP_tc SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_pf SEP_pn SEP_pt SEP_pc KR KL STOR TRW STO DF0 DN0 DTOT DLEN DND DR FDR FRR TST TSDL CT8 TH0 TC PCo FCo SHC CTX0 HDR B1M B1R R8 NQ NR PHI PNB PLO PAL TPE RA2 SPH SPA LO ST MI oldsh old tsd"] Theorem free_chitR_newfullF : forall (tk : ftail) (gn gf gl gqb : Z) (glnx : word) (nb fb lb qb nx bsz : Z) (ks : list word) (statv bj0 bj1 bj2 bj3 : word) (qmin : Z),
    tail_pre tk gn gf gl gqb glnx m -> tail_okR tk gn gqb (qb + (n + 8192)) -> tail_apart tk gl thr p r8 n0 f0 [lb; b] ->
    0 <= qmin < 2^64 -> ro_cells rsegs m (QINST + 64) [C8 (wz (2^28)); C8 (wz qmin)] ->
    (tk = TA -> apart gl 24 ri 4096 /\ apart gl 24 (sb + 24 * 2^32 + 3758096384) (4 * 2^27)) ->
    nb <> 0 -> 0 <= nb < 2^40 -> 0 <= fb < 2^64 -> 0 <= qb -> thr mod 16 = 0 -> length ks = 16%nat ->
    kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling -> lb + 8192 <= fa ->
    apart lb 8192 thr 4096 -> apart lb 8192 (p + -16) (8 * r8 + 16) -> apart lb 8192 ctx 0x10000 ->
    apart lb 8192 n0 kDepotNodesBlock -> apart lb 8192 f0 kStackStoreBlockBytes -> apart lb 8192 ri 4096 -> apart b 8192 lb 8192 ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m 0xb1d88 [C8 (wz ri)] ->
    rw_cells rsegs m (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    rw_cells rsegs m (thr + 208 + 1920) [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (thr + 208 + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] -> rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 72) [C8 na] ->
    u32arr rsegs m (fa + 4 * (nf - 1)) [w] ->
    rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    evt rsegs (free_chitR_newfullF_post tk gn gf gl gqb nb fb lb qb bsz qmin ks)
        (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz AINST) (wz p) a2 a3 (wz sto) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz dealloc_entry) fc None m (seg_rom rsegs)).
  Proof. natz_kl_box.
    intros until qmin. intros TPRE TOK TAP QMR QMM TAPR NB0 NBR FBR QB0 THRA LKS LBL LBH LBFA Alt Alp Alc Aln Alf Alr Abl SBC RIC QC LB PC24 STA MXc NFCc NALc FARRc BC.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    assert (QBN : qb + (n + 8192) < 2^64) by (destruct tk; cbn [tail_okR] in TOK; [destruct TOK| |]; lia).
    (* [comment removed for export] *)
    pose proof (HEAD nb fb lb qb nx bsz ks statv bj0 bj1 bj2 bj3) as HD.
    eapply evt_cut; [exact (HD NB0 ltac:(lia) QB0 QBN THRA LKS LBL LBH LBFA Alt Alp Alc Aln Alf Alr Abl SBC RIC QC LB PC24 STA MXc NFCc NALc FARRc BC)|].
    intros ms' PO. exact (free_chitR_newfullF_tl tk gn gf gl gqb glnx nb fb lb qb nx bsz ks statv bj0 bj1 bj2 bj3 qmin ms' TPRE TOK TAP QMR QMM TAPR NB0 NBR FBR QB0 THRA LKS LBL LBH LBFA Alt Alp Alc Aln Alf Alr Abl SBC RIC QC LB PC24 STA MXc NFCc NALc FARRc BC PO).
  Qed.
End FreeHitCore.
