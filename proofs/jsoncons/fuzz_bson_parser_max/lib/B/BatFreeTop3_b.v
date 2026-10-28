(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b BatPoison_b BatPoisonRun_b BatPoison3_b BatAllocA_b BatAllocB_b BatAllocG_b BatAllocV_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatCellEx_b BatByteCell_b BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b BatUnwind_b BatUnwindG_b BatAllocate3_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFxInit_b BatFxIcpt_b BatFxDealloc_b BatFxPut_b BatFxBatch2_b BatFxBatch3_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_free3_fp (S t p q16 qr l2 blk : Z) (x : Z) : Prop :=
  (S - 4096 <= x < S) \/ (p - 16 <= x < p - 12) \/ (p <= x < p + 8) \/ (t + 2824 <= x < t + 2840)
  \/ (2147450880 + 2 * q16 <= x < 2147450880 + 2 * q16 + qr) \/ dprivD l2 blk x
  \/ (0x140e40 <= x < 0x140e40 + 0x81030) \/ (0x1cf6c8 <= x < 0x1cf6c8 + 4).
Definition art_free3_W (S t p q16 qr l2 blk : Z) : list (Z * Z) :=
  [ (S - 4096, 4096); (t + 3168, 1); (p - 16, 4); (p, 8); (t + 2824, 16); (2147450880 + 2 * q16, qr);
    (0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (0x140e40, 0x81030); (0x1cf6c8, 4) ].

(* [comment removed for export] *)
Definition art_free3_epi (M : word -> option byte) (S p : Z) (raw0 : word) (regs : bvmap 5 word) : Prop :=
  cellA M (S - 2136) 8 0x799cc /\ cellA M (S - 2144) 8 S /\ cellA M (S - 2152) 8 p /\ cellA M (S - 2160) 8 0x7995c /\ cellA M (S - 2168) 8 1
  /\ cellA M (S - 2176) 8 (S - 2128) /\ cellA M (S - 2184) 8 (S - 81) /\ cellA M (S - 2192) 8 (U (getr regs 22))
  /\ cellA M (S - 8) 8 (U raw0) /\ cellA M (S - 16) 8 (U (getr regs 8)) /\ cellA M (S - 24) 8 (U (getr regs 9)) /\ cellA M (S - 32) 8 (U (getr regs 18))
  /\ cellA M (S - 40) 8 (U (getr regs 19)) /\ cellA M (S - 48) 8 (U (getr regs 20)) /\ cellA M (S - 56) 8 (U (getr regs 21)).

(* [comment removed for export] *)
Lemma art_enq_fp_zone : forall newb sp t spb ris qs km b L B cntB x,
  0 <= km -> 262144 * km <= 3758096384 -> ris = spb + 2 ^ 37 -> (L <> 0 -> 0 <= cntB <= 1021) ->
  (newb = true -> spb + 24 * 2 ^ 32 <= b /\ b + 8192 <= spb + 24 * 2 ^ 32 + 3758096384) ->
  (L <> 0 -> spb + 24 * 2 ^ 32 <= B /\ B + 8192 <= spb + 24 * 2 ^ 32 + 3758096384) -> (newb = false -> L <> 0) ->
  art_enq_fp newb sp t spb ris qs km b L B cntB x ->
  (sp - 736 <= x < sp) \/ (t <= x < t + 4096) \/ (ris <= x < ris + 4096) \/ (spb + 24 * 2 ^ 32 <= x < spb + 25 * 2 ^ 32)
  \/ (2147450880 + 8192 * qs + 24 * 2 ^ 29 <= x < 2147450880 + 8192 * qs + 25 * 2 ^ 29).
Proof.
  intros newb sp t spb ris qs km b L B cntB x Hkm Hkm' Eris Hcnt Hb HB HnL F.
  unfold art_enq_fp in F. destruct newb.
  - specialize (Hb eq_refl). unfold art_enq_new_fp, art_refill_fp in F.
    destruct F as [F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|[F|[F|[F|F]]]]]; try lia;
      first [ destruct F as (c' & Hc' & F); lia | destruct F as [NL F]; specialize (HB NL); lia ].
  - specialize (HB (HnL eq_refl)). specialize (Hcnt (HnL eq_refl)). destruct F as [F|[F|[F|F]]]; lia.
Qed.

(* [comment removed for export] *)
Lemma art_layout_tr : forall W M M', art_agree W M M' -> art_gap W 0x10000 (0x140938 - 0x10000) -> art_gap W 0x1d1768 512 -> art_layout M -> art_layout M'.
Proof.
  intros W M M' A G1 G2 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15).
  unfold art_layout. unfold SB, kHighMemEnd in *.
  repeat split; (apply (art_cell_tr W M M'); [exact A| first [eapply art_gap_sub; [exact G1|lia|cbn; lia] | eapply art_gap_sub; [exact G2|lia|cbn; lia]] |lia|cbn; lia|assumption]).
Qed.
Lemma art_prim_consts_tr : forall W M M' spb ris, art_agree W M M' -> art_gap W 0x10000 (0x140938 - 0x10000) -> art_gap W 0x1cf6e0 8 -> art_gap W 0x1d1768 512 ->
  art_prim_consts spb ris M -> art_prim_consts spb ris M'.
Proof.
  intros W M M' spb ris A G1 G2 G3 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  unfold art_prim_consts.
  repeat split; (apply (art_cell_tr W M M'); [exact A| first [eapply art_gap_sub; [exact G1|lia|cbn; lia] | eapply art_gap_sub; [exact G2|lia|cbn; lia] | eapply art_gap_sub; [exact G3|lia|cbn; lia]] |lia|cbn; lia|assumption]).
Qed.

(* [comment removed for export] *)
Lemma art_f3_poison_mem : forall M sp ra s0 s1 s2 s3 s4 s5 a k v, 64 <= sp -> sp < 2 ^ 64 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  let M' := Wf (art_poison_frame M sp ra s0 s1 s2 s3 s4 s5) a k v in
  mem_grows M M' /\ art_agree [(sp - 64, 64); (a, Z.of_nat k)] M M'.
Proof.
  intros M sp ra s0 s1 s2 s3 s4 s5 a k v H1 H2 H3 H4 M'. unfold M', art_poison_frame. split; [zgrows|].
  eapply art_agree_sub; [eapply art_agree_trans; [|apply art_agree_Wf; [exact H3|exact H4]]; zagree|]. zsub.
Qed.

(* [comment removed for export] *)
Definition art_free3_out (M0 M' : word -> option byte) (S t p q16 qr l2 blk b1 n spb ris qs km L B cntB bszB bytes : Z) (kb : nat) (inited : bool) (cl : art_cls) : Prop :=
  let c := t + 80 in
  let ca := t + 208 in
  let b := spb + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl in
  let newb := art_enq_newb L cntB in
  mem_grows M0 M'
  /\ (forall x : word, ~ art_free3_fp S t p q16 qr l2 blk (U x) -> ~ art_enq_fp newb (S - 2208) t spb ris qs km b L B cntB (U x) -> M' x = M0 x)
  /\ DInvD l2 blk kb M'
  /\ cellA M' (p - 16) 4 (3 + 256 * b1)
  /\ cellA M' 0x1cf6c8 4 1 /\ (forall k, 0 <= k < 2 ^ 15 -> cellA M' (0x140e48 + 8 * k) 8 0)
  /\ art_pc_hdr ca (if newb then true else inited) M' /\ art_cls_rep ca spb ris 24 (art_enq_cls newb cl) M' /\ art_cls_ok 24 (art_enq_cls newb cl)
  /\ (newb = true ->
        art_cptr_ok 8192 (cl_au (art_ca_pre 24 cl)) (art_ca_cptr 24 cl)
        /\ (cl_cache cl = [] -> art_cls_needs_populate 24 cl = true ->
              forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 32768 * km + j) 1 250)
        /\ cellA M' b 8 0 /\ cellA M' (b + 8) 8 (n + 8192) /\ cellA M' (b + 16) 8 1 /\ cellA M' (b + 24) 8 (p - 16)
        /\ cellA M' c 8 (L + 1) /\ cellA M' (c + 16) 8 b /\ (L = 0 -> cellA M' (c + 8) 8 b) /\ (L <> 0 -> cellA M' B 8 b))
  /\ (newb = false -> cellA M' (B + 16) 8 (cntB + 1) /\ cellA M' (B + 8) 8 (bszB + n) /\ cellA M' (B + 24 + 8 * cntB) 8 (p - 16))
  /\ cellA M' (c + 24) 8 (bytes + n + (if newb then 8192 else 0)).

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_free3_tail : forall regs regsD (M rom : word -> option byte) (raw0 : word) (S p : Z),
  getr regsD 2 = Z_to_bv 64 (S - 2208) -> ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 ->
  (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regsD r = getr regs r) ->
  art_free3_epi M S p raw0 regs ->
  exists regs',
    msteps ASEGS (mkst regsD (0x56a84 : word) M rom) (mkst regs' raw0 M rom)
    /\ getr regs' 2 = Z_to_bv 64 S /\ getr regs' 1 = raw0
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs regsD M rom raw0 S p H2 Hret HS HS' Hp KD (E36 & E44 & E52 & E60 & E68 & E76 & E84 & E92 & F8 & F16 & F24 & F32 & F40 & F48 & F56).
  pose proof (art_fx_fq2e_fn regsD M rom raw0 S p (U (getr regs 22)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
                H2 Hret HS HS' Hp (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
                E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56) as RUN.
  eexists. split; [exact RUN|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; try apply Z_to_bv_bv_unsigned; apply KD; inl.
Qed.

#[using="Type"] Theorem art_free3 :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M0 rom : word -> option byte) (raw0 : word)
         (S HI p q16 n qr b1 tp key tsd ctx t spb ris qs km l2 blk top bot L B wB cntB bszB bytes : Z) (kb : nat) (ia inited : bool) (cl : art_cls),
    let c := t + 80 in
    let ca := t + 208 in
    let b := spb + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl in
    let newb := art_enq_newb L cntB in
    let bytes' := bytes + n + (if newb then 8192 else 0) in
    getr regs 1 = raw0 -> ret_ok raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 p ->
    (* [comment removed for export] *)
    0x696000 + 16 <= p -> p = 16 * q16 -> 1 <= n < 2 ^ 28 -> n <= 8 * qr <= n + 7 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
    (art_poison_lo_ok p (8 * qr) \/ art_poison_hi_ok p (8 * qr)) ->
    (* [comment removed for export] *)
    art_geo HI t ctx tp tsd spb ris qs -> HI + 4096 <= S - 4096 -> S < 2 ^ 47 -> S mod 16 = 0 ->
    0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 -> 0x661b28 <= tp - 88 -> 0x661b28 <= tsd ->
    l2 + 2 ^ 20 <= HI -> blk + 2 ^ 23 <= HI ->
    apart l2 (2 ^ 20) t 4096 -> apart l2 (2 ^ 20) ctx 4096 -> apart l2 (2 ^ 20) spb (2 ^ 37 + 4096) -> apart l2 (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
    apart blk (2 ^ 23) t 4096 -> apart blk (2 ^ 23) ctx 4096 -> apart blk (2 ^ 23) spb (2 ^ 37 + 4096) -> apart blk (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
    (* [comment removed for export] *)
    p + 8 <= HI -> apart (p - 16) 24 t 4096 -> apart (p - 16) 24 ctx 4096 -> apart (p - 16) 24 l2 (2 ^ 20) -> apart (p - 16) 24 blk (2 ^ 23) ->
    apart (p - 16) 24 ris 4096 -> apart (p - 16) 24 (spb + 24 * 2 ^ 32 + 3758096384) (2 ^ 29) -> (L <> 0 -> apart (p - 16) 24 B 8192) ->
    (* [comment removed for export] *)
    wrA M0 (S - 4096) 4096 -> readable8 M0 S top -> wrA M0 t 4096 -> wrA M0 (p - 16) 24 -> wrA M0 (2147450880 + 2 * q16) qr ->
    wrA M0 0x1cf6c8 4 -> wrA M0 0x140e40 0x81030 ->
    art_layout M0 -> art_tsd M0 tp key tsd ctx t -> art_prim_consts spb ris M0 ->
    cellA M0 0x140918 1 1 -> cellA M0 0x14093c 4 30 -> cellA M0 (0x1d1768 + 34) 1 1 -> cellA M0 (t + 3168) 1 0 -> cellA M0 (t + 40) 1 0 ->
    cellA M0 (t + 8) 8 top -> cellA M0 (t + 16) 8 bot ->
    cellA M0 0x1cf6c8 4 (if ia then 1 else 0) -> (ia = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M0 (0x140e48 + 8 * k) 8 0) ->
    cellA M0 (p - 16) 4 (2 + 256 * b1) -> cellA M0 (p - 12) 4 n ->
    cellA M0 0x1d1708 8 0 -> cellA M0 t 8 ctx -> cellA M0 (ctx + 8) 4 0 ->
    cellA M0 (0x13c8b0 + 80) 8 (2 ^ 20) -> cellA M0 (0x13c8b0 + 64) 8 (2 ^ 28) -> cellA M0 (0x13d438 + 48) 4 0 ->
    (* [comment removed for export] *)
    art_pc_hdr ca inited M0 -> art_cls_rep ca spb ris 24 cl M0 -> art_cls_ok 24 cl -> (cl_cache cl <> [] -> inited = true) -> cl_mu cl = 262144 * km ->
    (newb = true -> cl_cache cl = [] -> art_cls_needs_populate 24 cl = true ->
       cl_mu cl + 262144 <= 3758096384
       /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new 24 cl) <= 536870912
       /\ wrA M0 (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 32768 * km) 32768
       /\ wrA M0 (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 469762048) 67108864) ->
    art_evok_list EVOK log (art_enq_events newb spb cl) ->
    0 <= L < 2 ^ 63 -> 0 <= B < 2 ^ 63 -> 0 <= bytes -> bytes + n + 8192 < 2 ^ 64 ->
    cellA M0 c 8 L -> cellA M0 (c + 24) 8 bytes ->
    (L <> 0 -> B = spb + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au cl) wB /\ ~ In wB (cl_cache cl ++ cl_free cl)
               /\ cellA M0 (c + 16) 8 B /\ cellA M0 (B + 16) 8 cntB /\ cellA M0 (B + 8) 8 bszB /\ 0 <= cntB <= 1021 /\ 0 <= bszB /\ bszB + n < 2 ^ 64) ->
    (forall x, p - 16 <= x < p - 12 -> ~ art_enq_fp newb (S - 2208) t spb ris qs km b L B cntB x) ->
    (* [comment removed for export] *)
    DInvD l2 blk (Datatypes.S kb) M0 -> DRoD M0 ->
    (* [comment removed for export] *)
    (forall regs' (M' : word -> option byte),
        getr regs' 2 = Z_to_bv 64 S -> getr regs' 1 = raw0 ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        bytes' <= 2 ^ 20 ->
        art_free3_out M0 M' S t p q16 qr l2 blk b1 n spb ris qs km L B cntB bszB bytes kb inited cl ->
        Q (log ++ art_enq_events newb spb cl) (mkst regs' raw0 M' rom)) ->
    (* [comment removed for export] *)
    (forall regs' (M' : word -> option byte),
        getr regs' 1 = (0x56a84 : bv 64)%bv -> getr regs' 2 = Z_to_bv 64 (S - 2208) ->
        getr regs' 10 = Z_to_bv 64 0x13c8b0 -> getr regs' 11 = Z_to_bv 64 c -> getr regs' 12 = Z_to_bv 64 ca -> getr regs' 13 = Z_to_bv 64 (S - 2128) ->
        (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        2 ^ 20 < bytes' ->
        art_free3_out M0 M' S t p q16 qr l2 blk b1 n spb ris qs km L B cntB bszB bytes kb inited cl ->
        art_free3_epi M' S p raw0 regs -> wrA M' (S - 4096) 4096 ->
        aruns ASEGS EVOK GR Q (log ++ art_enq_events newb spb cl) (mkst regs' (0x542b0 : word) M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x79824 : word) M0 rom).
Proof.
  intros Q log regs M0 rom raw0 S HI p q16 n qr b1 tp key tsd ctx t spb ris qs km l2 blk top bot L B wB cntB bszB bytes kb ia inited cl c ca b newb bytes'
         H1 Hret H2 H4 H10 Hp Ep Hn Hqr Hb1 Hb14 POK
         GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Htpd Htsdd
         Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
         HpHI Apt Apc Apl2 Apblk Apris Apfa ApB
         W RD0 Wt Wp Wsh Wia Wtab LY TSD PC
         Ci Cctx30 Cfast Cunw C40 Ctop Cbot Cia Ctab Chw Cn Cfh Ctctx Ctid Cqc Cqm Cff
         PH RC OK Hin Emu Room EV HL HB Hby Hby' CL Cby LBn HP24 DI DR KX1 KX2.
  assert (Ec : c = t + 80) by reflexivity. assert (Eca : ca = t + 208) by reflexivity.
  assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl) by reflexivity.
  assert (Ebytes' : bytes' = bytes + n + (if newb then 8192 else 0)) by reflexivity.
  subst c ca. clearbody b bytes'.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G15; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
  change (hid (t + 4096 <= 0x10000 \/ 0x696000 <= t)) in G9. change (hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx)) in G15.
  clear G10 G16.
  pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
  assert (Hkm : 0 <= km) by lia. assert (Hkm' : 262144 * km <= 3758096384) by lia.
  pose proof DI as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _).
  pose proof TSD as (_ & _ & _ & _ & _ & TR).
  pose proof PC as (_ & _ & _ & _ & _ & Cpg1 & Cpg2 & _).
  assert (Hsh : 2147450880 <= 2147450880 + 2 * q16 /\ 2147450880 + 2 * q16 + qr <= 0x10007fff8000).
  { clear - POK Ep Hp Hn Hqr. unfold art_poison_lo_ok, art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd in POK. lia. }
  assert (Aps : apart (p - 16) 24 (2147450880 + 2 * q16) qr).
  { unfold apart. clear - POK Ep Hp Hn Hqr. unfold art_poison_lo_ok, art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd in POK. lia. }
  assert (HS8 : S mod 8 = 0). { clear - HS16. rewrite <- (Z.div_exact S 16) in HS16 by lia. rewrite HS16. replace (16 * (S / 16)) with ((2 * (S / 16)) * 8) by lia. apply Z_mod_mult. }
  (* [comment removed for export] *)
  pose proof (art_fi_a_fn regs M0 rom raw0 S p H1 H2 H10 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) HS47 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) W) as RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R _ ?X _) => set (r1 := R) in RUN1; set (M1 := X) in RUN1 end.
  eapply ar_steps; [exact RUN1|].
  assert (G01 : mem_grows M0 M1) by (unfold M1, art_fi_mem; zgrows).
  assert (A01 : art_agree [(S - 4096, 4096)] M0 M1).
  { unfold M1, art_fi_mem. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. eapply art_agree_sub; [zagree|]. intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia. }
  assert (F8 : cellA M1 (S - 8) 8 (U raw0)) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell).
  assert (F16 : cellA M1 (S - 16) 8 (U (getr regs 8))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell).
  assert (F24 : cellA M1 (S - 24) 8 (U (getr regs 9))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell).
  assert (F32 : cellA M1 (S - 32) 8 (U (getr regs 18))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell).
  assert (F40 : cellA M1 (S - 40) 8 (U (getr regs 19))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell).
  assert (F48 : cellA M1 (S - 48) 8 (U (getr regs 20))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell).
  assert (F56 : cellA M1 (S - 56) 8 (U (getr regs 21))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell).
  (* [comment removed for export] *)
  destruct (art_ia_run r1 M1 rom (0x79858 : bv 64)%bv (S - 2128) ia
              ltac:(unfold r1; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold r1; gres; reflexivity)
              ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia)
              ltac:(eapply wr_grows; [exact G01|]; eapply wr_sub; [exact W|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A01); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cia]) ltac:(eapply wr_grows; [exact G01|exact Wia]) ltac:(eapply wr_grows; [exact G01|exact Wtab])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A01); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cpg1]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A01); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cpg2])
              ltac:(intros Eia k Hk; apply (art_cell_tr1 _ _ _ _ _ _ A01); [revert Hk; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; intros Hk; zarith_t|exact (Ctab Eia k Hk)]))
    as (r2 & M2 & RUN2 & P2_10 & P2_1 & P2_2 & K2 & G12 & A12 & Cia2 & Ctab2).
  eapply ar_steps; [exact RUN2|].
  replace (S - 2128 - 48) with (S - 2176) in A12 by (clear; lia).
  pose proof (art_agree_trans _ _ _ _ _ A01 A12) as A02. cbn [app] in A02.
  assert (G02 : mem_grows M0 M2) by (eapply mem_grows_trans; [exact G01|exact G12]).
  (* [comment removed for export] *)
  assert (T2 : art_tsd M2 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M2 tp key tsd ctx t A02); [| | | |exact TSD]; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t. }
  destruct (art_fi_b r2 M2 rom S p (p / 2 ^ 32) tp key tsd ctx t top bot
              P2_2 ltac:(rewrite K2 by inl; unfold r1; gres; exact H4) ltac:(rewrite K2 by inl; unfold r1; gres; reflexivity) ltac:(rewrite K2 by inl; unfold r1; gres; reflexivity) P2_10
              ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) HS47 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(apply Z.div_mod; clear; lia)
              G7 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) G9 ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) G15 G18 G19 G20 G21 G22 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) Htop
              ltac:(eapply wr_grows; [exact G02|exact W]) ltac:(eapply wr_grows; [exact G02|exact Wt]) T2
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Ci])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cctx30])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|pose proof LY as L'; unfold art_layout in L'; tauto])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cfast])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cunw])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact C40])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Ctop])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cbot])
              ltac:(replace (0x140e40 + 8 + 8 * (p / 2 ^ 32)) with (0x140e48 + 8 * (p / 2 ^ 32)) by (clear; lia); apply Ctab2;
                    split; [apply Z.div_pos; [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia|clear; lia] | apply Z.div_lt_upper_bound; [clear; lia|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia]]))
    as (r3 & M3 & RUN3 & Q3_1 & Q3_2 & Q3_10 & Q3_11 & Q3_12 & Q3_13 & Q3_14 & Q3_15 & Q3_24 & Q3_4 & K3 & G23 & A23p
        & E36 & E44 & E52 & E60 & E68 & E76 & E84 & E92 & E00 & E08 & E28 & E20 & E16' & W3).
  eapply ar_steps; [exact RUN3|].
  assert (E22 : getr r2 22 = getr regs 22) by (rewrite K2 by inl; unfold r1; gres; reflexivity).
  assert (E23 : getr r2 23 = getr regs 23) by (rewrite K2 by inl; unfold r1; gres; reflexivity).
  assert (E24 : getr r2 24 = getr regs 24) by (rewrite K2 by inl; unfold r1; gres; reflexivity).
  rewrite E22 in E92. rewrite E23 in E00. rewrite E24 in E08.
  assert (A23 : art_agree [(S - 2272, 2208); (t + 3168, 1)] M2 M3).
  { intros x Hx. cbn [art_out fst snd] in Hx. apply A23p; clear - Hx; lia. }
  pose proof (art_agree_trans _ _ _ _ _ A02 A23) as A03. cbn [app] in A03.
  assert (G03 : mem_grows M0 M3) by (eapply mem_grows_trans; [exact G02|exact G23]).
  (* [comment removed for export] *)
  assert (RD3 : readable8 M3 (S - 16) top).
  { intros a Ha1 Ha2 Ha8. destruct (Z.lt_ge_cases a S) as [Lo|Hi].
    - assert (a = S - 16 \/ a = S - 8) as [->| ->].
      { clear - Ha1 Lo Ha8 HS8. rewrite <- (Z.div_exact a 8) in Ha8 by lia. rewrite <- (Z.div_exact S 8) in HS8 by lia. lia. }
      + eexists. apply (art_cell_tr1 _ M2 M3 _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|]. apply (art_cell_tr1 _ M1 M2 _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|]. exact F16.
      + eexists. apply (art_cell_tr1 _ M2 M3 _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|]. apply (art_cell_tr1 _ M1 M2 _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|]. exact F8.
    - destruct (RD0 a ltac:(lia) ltac:(lia) Ha8) as [w' Cw]. exists w'. apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Cw].
      revert Hi Ha2. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Hi Ha2. zarith_t. }
  destruct (art_unwind_fast_any r3 M3 rom (0x81f98 : bv 64)%bv (S - 2208) (S - 2128) 0x7995c S top bot
              Q3_1 ltac:(unfold ret_ok; bveq) Q3_2 Q3_10 Q3_11 Q3_12 Q3_13 Q3_14 Q3_15
              ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear; lia) ltac:(clear; lia) Hbot Hbt Htop4 Htop ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) HS8 ltac:(clear; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia)
              ltac:(eapply wr_sub; [exact W3|clear; lia|clear; lia]) ltac:(eapply wr_sub; [exact W3|clear; lia|clear; lia]) (fun _ _ => RD3)
              ltac:(apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cpg1]) ltac:(apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cpg2]))
    as (r4 & M4 & RUN4 & Q4_2 & Q4_1 & K4 & G34 & A34p & (sz & Hsz & Csz & TRC)).
  eapply ar_steps; [exact RUN4|].
  assert (A34 : art_agree [(S - 2120, 4); (S - 2112, 240); (S - 2272, 64)] M3 M4).
  { intros x Hx. cbn [art_out fst snd] in Hx. apply A34p; clear - Hx; lia. }
  pose proof (art_agree_trans _ _ _ _ _ A03 A34) as A04. cbn [app] in A04.
  assert (G04 : mem_grows M0 M4) by (eapply mem_grows_trans; [exact G03|exact G34]).
  (* [comment removed for export] *)
  assert (Wt4 : wrA M4 t 4096) by (eapply wr_grows; [exact G04|exact Wt]).
  pose proof At_i as At_i'. unfold apart in At_i'.
  destruct (art_cell_exists M4 (t + 2824) 8 ltac:(clear; lia) ltac:(clear - At_i'; cbn; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; cbn; lia)
              ltac:(eapply wr_sub; [exact Wt4|clear; lia|clear; cbn; lia])) as (fr1 & Hfr1 & Cfr1).
  destruct (art_cell_exists M4 (t + 2832) 8 ltac:(clear; lia) ltac:(clear - At_i'; cbn; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; cbn; lia)
              ltac:(eapply wr_sub; [exact Wt4|clear; lia|clear; cbn; lia])) as (fr2 & Hfr2 & Cfr2).
  clear At_i'.
  assert (Csz8 : cellA M4 (S - 2120) 8 sz).
  { replace sz with (sz + 0 * 2 ^ 32) by (clear; lia). replace (S - 2128 + 8) with (S - 2120) in Csz by (clear; lia).
    apply cell8_of_cells4; [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia|clear - Hsz; lia|clear; lia|exact Csz|].
    replace (S - 2120 + 4) with (S - 2116) by (clear; lia). apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E16']. }
  pose proof (art_fx_fcu2_fn r4 M4 rom S p b1 n sz t tp key tsd ctx fr1 fr2 (U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24))
               Q4_2 ltac:(rewrite K4 by inl; exact Q3_24) ltac:(rewrite K4 by inl; exact Q3_4)
               ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) HS47 Hp ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(rewrite Ep, Z.mul_comm; apply Z_mod_mult) Hb1 Hb14 ltac:(clear - Hn; lia) Hsz
               G7 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) Apt ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) G18 Apc G15 G9 G19 G20 G21 G22
               Hfr1 Hfr2 (u64_range _) (u64_range _) (u64_range _)
               ltac:(eapply wr_grows; [exact G34|exact W3]) Wt4 ltac:(eapply wr_grows; [exact G04|exact Wp])
               ltac:(apply (art_tsd_tr _ M0 M4 tp key tsd ctx t A04); [| | | |exact TSD]; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t)
               ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E36]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E44]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E52]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E60]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E68]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E76]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E84]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E92]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E00]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E08]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact E28]) Csz8
               ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A04); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Chw]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A04); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cn]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A04); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cfh]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A04); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Ctctx]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A04); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Ctid]) Cfr1 Cfr2) as RUN5.
  match type of RUN5 with msteps _ _ (mkst ?R _ ?X _) => set (r5 := R) in RUN5; set (M5 := X) in RUN5 end.
  eapply ar_steps; [exact RUN5|].
  assert (G45 : mem_grows M4 M5) by (unfold M5, art_fx_fcu2_mem; zgrows).
  assert (A45 : art_agree [(S - 4096, 4096); (t + 3168, 1); (p - 16, 4); (p, 8); (t + 2824, 16)] M4 M5).
  { unfold M5, art_fx_fcu2_mem. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. eapply art_agree_sub; [zagree|]. intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia. }
  pose proof (art_agree_trans _ _ _ _ _ A04 A45) as A05. cbn [app] in A05.
  assert (G05 : mem_grows M0 M5) by (eapply mem_grows_trans; [exact G04|exact G45]).
  (* [comment removed for export] *)
  assert (DI5 : DInvD l2 blk (Datatypes.S kb) M5).
  { apply (DInvD_frame l2 blk (Datatypes.S kb) M0 M5 DI). intros x Dx. apply A05. revert Dx. apply art_dpriv_out; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t. }
  assert (DR5 : DRoD M5).
  { destruct DR as (D1 & D2 & D3). unfold DRoD. repeat split; (apply (art_cell_tr1 _ M0 M5 _ _ _ A05); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|assumption]). }
  assert (DP5 : DPreD blk M5 (S - 2112) sz).
  { unfold DPreD. split; [exact Hsz|]. split.
    { clear - HS8. rewrite <- (Z.div_exact S 8) in HS8 by lia. rewrite HS8. replace (8 * (S / 8) - 2112) with ((S / 8 - 264) * 8) by lia. apply Z_mod_mult. }
    split; [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia|]. split; [revert Hsz; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; intros Hsz; lia|]. split; [unfold apart; revert Hsz; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; intros Hsz; lia|].
    intros i Hi. destruct (TRC i Hi) as [w' Cw]. unfold rcell. eexists.
    assert (C5' : cellA M5 (S - 2112 + 8 * i) 8 (U w')).
    { replace (S - 2128 + 16 + 8 * i) with (S - 2112 + 8 * i) in Cw by (clear; lia). unfold M5, art_fx_fcu2_mem. revert Hsz Hi Cw. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Hsz Hi Cw. zcell. }
    exact C5'. }
  assert (W5 : wrA M5 (S - 2176 - 224) 224) by (eapply wr_grows; [exact G05|]; eapply wr_sub; [exact W|clear; lia|clear; lia]).
  assert (ND5 : nodp (dprivD l2 blk) (S - 2176 - 224) 224). { intros i Hi D. unfold dprivD in D. revert Hi D. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Hi D. lia. }
  pose proof (art_depot_spec_holds l2 blk) as DEPOT. unfold art_depot_spec in DEPOT.
  destruct (DEPOT kb r5 M5 rom (0x56888 : bv 64)%bv (S - 2176) (S - 2112) sz ltac:(unfold r5; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r5; gres; reflexivity)
              ltac:(unfold r5; gres; reflexivity) ltac:(unfold r5; gres; reflexivity) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) W5 ND5 DI5 DP5 DR5)
    as (r6 & M6 & id & RUN6 & P6_10 & Hid & K6 & G56 & AGd & DI6).
  clear DEPOT.
  eapply ar_steps; [exact RUN6|].
  assert (A56 : art_agree [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (S - 2176 - 224, 224)] M5 M6).
  { intros x Hx. cbn [art_out fst snd] in Hx. apply AGd; [unfold dprivD; clear - Hx; lia | clear - Hx; lia]. }
  pose proof (art_agree_trans _ _ _ _ _ A05 A56) as A06. cbn [app] in A06.
  assert (G06 : mem_grows M0 M6) by (eapply mem_grows_trans; [exact G05|exact G56]).
  assert (KK6 : forall r v, art_depot_kept r -> getr r5 r = v -> getr r6 r = v). { intros r v Kr E. rewrite K6 by exact Kr. exact E. }
  (* [comment removed for export] *)
  assert (T56 : forall a (k : nat) v, S - 2176 <= a -> a + Z.of_nat k <= S -> cellA M5 a k v -> cellA M6 a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr1 _ M5 M6 a k v A56); [|exact C]. revert Ha Hk. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Ha Hk. zarith_t. }
  pose proof (art_fx_fq1_fn r6 M6 rom S p b1 n t id (U (getr regs 22))
               ltac:(apply KK6; [dk8|]; unfold r5; gres; reflexivity) ltac:(apply KK6; [dk8|]; unfold r5; gres; reflexivity) ltac:(apply KK6; [dk8|]; unfold r5; gres; reflexivity) P6_10
               ltac:(apply KK6; [dk8|]; unfold r5; gres; reflexivity) ltac:(apply KK6; [dk8|]; unfold r5; gres; reflexivity) ltac:(apply KK6; [dk8|]; unfold r5; gres; reflexivity)
               ltac:(apply KK6; [dk8|]; unfold r5; gres; reflexivity) ltac:(apply KK6; [dk8|]; unfold r5; gres; reflexivity)
               ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) HS47 Hp ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) Hb1 Hn Hid G7 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) (u64_range _)
               ltac:(eapply wr_grows; [exact G06|exact W]) ltac:(eapply wr_grows; [exact G06|exact Wp])
               ltac:(apply (art_layout_tr _ M0 M6 A06); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact LY])
               ltac:(apply T56; [clear; lia|clear; cbn; lia|unfold M5, art_fx_fcu2_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]) ltac:(apply T56; [clear; lia|clear; cbn; lia|unfold M5, art_fx_fcu2_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell])
               ltac:(apply T56; [clear; lia|clear; cbn; lia|unfold M5, art_fx_fcu2_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]) ltac:(apply T56; [clear; lia|clear; cbn; lia|unfold M5, art_fx_fcu2_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell])
               ltac:(apply T56; [clear; lia|clear; cbn; lia|unfold M5, art_fx_fcu2_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]) ltac:(apply T56; [clear; lia|clear; cbn; lia|unfold M5, art_fx_fcu2_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell])
               ltac:(apply (art_cell_tr1 _ M5 M6 _ _ _ A56); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|unfold M5, art_fx_fcu2_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell])
               ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A06); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cn]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A06); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cqc]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A06); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cqm]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A06); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cff])) as RUN7.
  match type of RUN7 with msteps _ _ (mkst ?R _ ?X _) => set (r7 := R) in RUN7; set (M7 := X) in RUN7 end.
  eapply ar_steps; [exact RUN7|].
  assert (G67 : mem_grows M6 M7) by (unfold M7, art_fx_fq1_mem; zgrows).
  assert (A67 : art_agree [(S - 4096, 4096); (p, 8)] M6 M7).
  { unfold M7, art_fx_fq1_mem. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. eapply art_agree_sub; [zagree|]. intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia. }
  pose proof (art_agree_trans _ _ _ _ _ A06 A67) as A07. cbn [app] in A07.
  assert (G07 : mem_grows M0 M7) by (eapply mem_grows_trans; [exact G06|exact G67]).
  (* [comment removed for export] *)
  assert (Hrs : (n + 7) / 8 * 8 = 8 * qr). { replace ((n + 7) / 8) with qr; [clear; lia|]. apply (Z.div_unique _ 8 qr (n + 7 - 8 * qr)); clear - Hqr; lia. }
  assert (Hp8 : p / 8 = 2 * q16). { symmetry. apply (Z.div_unique _ 8 _ 0); clear - Ep; lia. }
  assert (Hq8 : 8 * qr / 8 = qr). { rewrite Z.mul_comm. apply Z.div_mul. clear; lia. }
  assert (Hqr0 : 0 <= qr) by (clear - Hn Hqr; lia).
  assert (E7_11 : getr r7 11 = Z_to_bv 64 (8 * qr)) by (unfold r7; gres; rewrite Hrs; reflexivity).
  destruct (art_poison3_run r7 M7 rom (0x56b34 : bv 64)%bv (S - 2208) p (8 * qr) 253
              ltac:(unfold r7; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r7; gres; reflexivity) ltac:(unfold r7; gres; reflexivity) E7_11 ltac:(unfold r7; gres; reflexivity)
              ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(eapply wr_grows; [exact G07|]; eapply wr_sub; [exact W|clear; lia|clear; lia]) ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia)
              ltac:(apply (art_layout_tr _ M0 M7 A07); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact LY])
              POK ltac:(rewrite Ep; replace (16 * q16) with ((2 * q16) * 8) by (clear; lia); apply Z_mod_mult) ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(clear - Hqr0; lia) ltac:(clear; lia)
              ltac:(intros E; exfalso; clear - E; lia)
              ltac:(rewrite Hq8, Hp8; unfold SB; eapply wr_grows; [exact G07|exact Wsh]))
    as (r8 & RUN8 & P8_10 & P8_1 & P8_2 & P8_8 & P8_9 & P8_18 & P8_19 & P8_20 & P8_21 & K8).
  rewrite Hq8, Hp8 in RUN8. unfold SB in RUN8.
  destruct (art_f3_poison_mem M7 (S - 2208) (U (0x56b34 : bv 64)%bv) (U (getr r7 8)) (U (getr r7 9)) (U (getr r7 18)) (U (getr r7 19)) (U (getr r7 20)) (U (getr r7 21))
              (2147450880 + 2 * q16) (Z.to_nat qr) 253 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(rewrite Z2Nat.id by exact Hqr0; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia)) as (G78 & A78).
  rewrite Z2Nat.id in A78 by exact Hqr0. replace (S - 2208 - 64) with (S - 2272) in A78 by (clear; lia).
  set (M8 := Wf (art_poison_frame M7 (S - 2208) (U (0x56b34 : bv 64)%bv) (U (getr r7 8)) (U (getr r7 9)) (U (getr r7 18)) (U (getr r7 19)) (U (getr r7 20)) (U (getr r7 21)))
                (2147450880 + 2 * q16) (Z.to_nat qr) 253) in *.
  clearbody M8.
  eapply ar_steps; [exact RUN8|].
  assert (KK8 : forall r v, art_poison_kept r -> getr r7 r = v -> getr r8 r = v). { intros r v Kr E. rewrite K8 by exact Kr. exact E. }
  assert (G08 : mem_grows M0 M8) by (eapply mem_grows_trans; [exact G07|exact G78]).
  pose proof (art_agree_trans _ _ _ _ _ A07 A78) as A08f. cbn [app] in A08f.
  assert (A08 : art_agree [ (S - 4096, 4096); (t + 3168, 1); (p - 16, 4); (p, 8); (t + 2824, 16); (2147450880 + 2 * q16, qr);
                            (0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (0x140e40, 0x81030); (0x1cf6c8, 4) ] M0 M8).
  { eapply art_agree_sub; [exact A08f|]. intros z. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Hz Hout. cbn [art_out app fst snd] in Hout |- *. repeat split; lia. }
  (* [comment removed for export] *)
  #[local] Ltac pk8 := unfold art_poison_kept; repeat split; discriminate.
  pose proof (art_fx_fq2a_fn r8 M8 rom (t + 80) (t + 208) (S - 2128) (p - 16) n
               ltac:(rewrite P8_9; unfold r7; gres; reflexivity) ltac:(rewrite P8_20; unfold r7; gres; reflexivity)
               ltac:(rewrite P8_19; unfold r7; gres; reflexivity) ltac:(rewrite P8_21; unfold r7; gres; reflexivity) ltac:(rewrite P8_18; unfold r7; gres; reflexivity)) as RUN9.
  match type of RUN9 with msteps _ _ (mkst ?R _ _ _) => set (r9 := R) in RUN9 end.
  eapply ar_steps; [exact RUN9|].
  (* [comment removed for export] *)
  assert (HnL : newb = false -> L <> 0).
  { intros E NL. unfold newb, art_enq_newb in E. rewrite NL in E. cbn in E. discriminate. }
  assert (PC8 : art_prim_consts spb ris M8) by (apply (art_prim_consts_tr _ M0 M8 spb ris A08); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact PC]).
  assert (LY8 : art_layout M8) by (apply (art_layout_tr _ M0 M8 A08); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact LY]).
  assert (T8 : art_tsd M8 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M8 tp key tsd ctx t A08); [| | | |exact TSD]; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t. }
  assert (PH8 : art_pc_hdr (t + 208) inited M8).
  { apply (art_pc_hdr_tr _ (t + 208) inited M0 M8 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) A08); [|exact PH]. intros c' Hc'. revert Hc'. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Hc'. zarith_t. }
  assert (RC8 : art_cls_rep (t + 208) spb ris 24 cl M8).
  { apply (art_cls_rep_tr [ (S - 4096, 4096); (t + 3168, 1); (p - 16, 4); (p, 8); (t + 2824, 16); (2147450880 + 2 * q16, qr); (0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (0x140e40, 0x81030); (0x1cf6c8, 4) ] (t + 208) spb ris 24 cl M0 M8); first [ exact RC | exact G08 | exact A08 | exact Hl16 | idtac ]; first [ clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia | clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t ]. }
  assert (Room8 : newb = true -> cl_cache cl = [] -> art_cls_needs_populate 24 cl = true ->
            cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new 24 cl) <= 536870912
            /\ wrA M8 (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 32768 * km) 32768 /\ wrA M8 (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 469762048) 67108864).
  { intros e1 e2 e3. destruct (Room e1 e2 e3) as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; eapply wr_grows; first [exact G08|assumption]. }
  assert (HBz : L <> 0 -> spb + 24 * 2 ^ 32 <= B /\ B + 8192 <= spb + 24 * 2 ^ 32 + 3758096384).
  { intros NL. destruct (LBn NL) as (EB & (Hw0 & Hw1 & _) & _). clear - EB Hw0 Hw1 Haumu Hmu3. lia. }
  assert (LBn8 : L <> 0 -> B = spb + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au cl) wB /\ ~ In wB (cl_cache cl ++ cl_free cl)
               /\ cellA M8 (t + 80 + 16) 8 B /\ cellA M8 (B + 16) 8 cntB /\ cellA M8 (B + 8) 8 bszB /\ 0 <= cntB <= 1021 /\ 0 <= bszB /\ bszB + n < 2 ^ 64).
  { intros NL. pose proof (HBz NL) as HBz'. pose proof (ApB NL) as ApB'. destruct (LBn NL) as (EB & CPB & NIB & CB16 & CBc & CBs & Hc1 & Hb0 & Hb1').
    split; [exact EB|]. split; [exact CPB|]. split; [exact NIB|].
    split; [apply (art_cell_tr1 _ _ _ _ _ _ A08); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact CB16]|].
    split; [apply (art_cell_tr1 _ _ _ _ _ _ A08); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5 HBz' ApB'; zarith_t|exact CBc]|].
    split; [apply (art_cell_tr1 _ _ _ _ _ _ A08); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5 HBz' ApB'; zarith_t|exact CBs]|].
    split; [exact Hc1|]. split; [exact Hb0|exact Hb1']. }
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
  apply (art_enqueue_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r9 M8 rom (0x56b4c : bv 64)%bv
           (S - 2208) HI t ctx tp key tsd spb ris qs km (S - 2128) (p - 16) n L B wB cntB bszB bytes inited cl
           ltac:(unfold r9; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold r9; gres; exact P8_2)
           ltac:(unfold r9; gres; apply KK8; [pk8|]; unfold r7; gres; apply KK6; [dk8|]; unfold r5; gres; rewrite K4 by inl; exact Q3_4)
           ltac:(unfold r9; gres; reflexivity) ltac:(unfold r9; gres; reflexivity) ltac:(unfold r9; gres; reflexivity) ltac:(unfold r9; gres; reflexivity) ltac:(unfold r9; gres; reflexivity)
           ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) GEO
           ltac:(eapply wr_grows; [exact G08|]; eapply wr_sub; [exact W|clear; lia|clear; lia]) ltac:(eapply wr_grows; [exact G08|exact Wt])
           PC8 LY8 T8 PH8 RC8 OK Hin Emu Room8 EV HL HB Hby Hby' ltac:(clear - Hn; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia)
           ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A08); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact CL]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A08); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cby]) LBn8).
  intros r10 M10 P10_2 P10_1 K10 G810 AG810 PH10 RC10 OK10 NEW10 OLD10 Cby10.
  fold newb in AG810, PH10, RC10, OK10, NEW10, OLD10, Cby10 |- *. rewrite <- ?Eb in AG810, NEW10.
  (* [comment removed for export] *)
  assert (Hbz : newb = true -> spb + 24 * 2 ^ 32 <= b /\ b + 8192 <= spb + 24 * 2 ^ 32 + 3758096384).
  { intros E. destruct (NEW10 E) as ((Hw0 & Hw1 & _) & _). pose proof OK10 as OK'. rewrite E in OK'. unfold art_enq_cls, art_cls_ok in OK'.
    cbn [art_cls_pop cl_cache cl_free cl_au cl_mu cl_mfa] in OK'. destruct OK' as (_ & (_ & Haumu') & _ & _ & _ & Hmu3' & _).
    rewrite Eb. clear - Hw0 Hw1 Haumu' Hmu3'. lia. }
  assert (ZONE : forall x, art_enq_fp newb (S - 2208) t spb ris qs km b L B cntB x ->
            (S - 2208 - 736 <= x < S - 2208) \/ (t <= x < t + 4096) \/ (ris <= x < ris + 4096) \/ (spb + 24 * 2 ^ 32 <= x < spb + 25 * 2 ^ 32)
            \/ (2147450880 + 8192 * qs + 24 * 2 ^ 29 <= x < 2147450880 + 8192 * qs + 25 * 2 ^ 29)).
  { intros x F. apply (art_enq_fp_zone newb (S - 2208) t spb ris qs km b L B cntB x Hkm Hkm' Eris); [ | exact Hbz | exact HBz | exact HnL | exact F ].
    intros NL. destruct (LBn NL) as (_ & _ & _ & _ & _ & _ & Hc1 & _). exact Hc1. }
  assert (Z_above : forall x, S - 2208 <= x -> ~ art_enq_fp newb (S - 2208) t spb ris qs km b L B cntB x).
  { intros x Hx F. apply ZONE in F. revert Hx F. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Hx F. lia. }
  assert (Z_img : forall x, 0x10000 <= x < 0x696000 -> ~ art_enq_fp newb (S - 2208) t spb ris qs km b L B cntB x).
  { intros x Hx F. apply ZONE in F. pose proof At_i as At_i'. unfold apart in At_i'. revert Hx F At_i'. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Hx F At_i'. lia. }
  assert (Z_dp : forall x, dprivD l2 blk x -> ~ art_enq_fp newb (S - 2208) t spb ris qs km b L B cntB x).
  { intros x D F. destruct D as [D|[D|D]].
    - apply (Z_img x); [clear - D; lia|exact F].
    - apply ZONE in F. pose proof Al2t as X1. pose proof Al2k as X2. pose proof Al2s as X3. unfold apart in X1, X2, X3. revert D F X1 X2 X3. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros D F X1 X2 X3. lia.
    - apply ZONE in F. pose proof Abt as X1. pose proof Abk as X2. pose proof Abs as X3. unfold apart in X1, X2, X3. revert D F X1 X2 X3. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros D F X1 X2 X3. lia. }
  assert (T810a : forall a (k : nat) v, S - 2208 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M8 a k v -> cellA M10 a k v).
  { intros a k v Ha Hk C. apply (art_cell_agree _ M8 M10); [|clear - Ha G1 HHI; lia|exact Hk|exact C]. intros x Hx. apply AG810. apply Z_above. clear - Hx Ha. lia. }
  assert (T810i : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x696000 -> cellA M8 a k v -> cellA M10 a k v).
  { intros a k v Ha Hk C. apply (art_cell_agree _ M8 M10); [|clear - Ha; lia|clear - Hk; lia|exact C]. intros x Hx. apply AG810. apply Z_img. clear - Hx Ha Hk. lia. }
  (* [comment removed for export] *)
  assert (T7_10 : forall a (k : nat) v, S - 2208 <= a -> a + Z.of_nat k <= S -> cellA M7 a k v -> cellA M10 a k v).
  { intros a k v Ha Hk C. apply T810a; [exact Ha|revert Hk; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; intros Hk; lia|]. apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact C]. revert Ha Hk. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Ha Hk. zarith_t. }
  assert (TF : forall a v, S - 56 <= a -> a + 8 <= S -> cellA M1 a 8 v -> cellA M7 a 8 v).
  { intros a v Ha Ha' C.
    assert (C4 : cellA M4 a 8 v).
    { apply (art_cell_tr1 _ M3 M4 _ _ _ A34); [revert Ha Ha'; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; intros Ha Ha'; zarith_t|]. apply (art_cell_tr1 _ M2 M3 _ _ _ A23); [revert Ha Ha'; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; intros Ha Ha'; zarith_t|].
      apply (art_cell_tr1 _ M1 M2 _ _ _ A12); [revert Ha Ha'; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; intros Ha Ha'; zarith_t|exact C]. }
    assert (C5 : cellA M5 a 8 v). { unfold M5, art_fx_fcu2_mem. revert Ha Ha' C4. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Ha Ha' C4. zcell. }
    assert (C6 : cellA M6 a 8 v). { apply T56; [clear - Ha; lia|clear - Ha'; cbn; lia|exact C5]. }
    unfold M7, art_fx_fq1_mem. revert Ha Ha' C6. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Ha Ha' C6. zcell. }
  assert (EPI : art_free3_epi M10 S p raw0 regs).
  { unfold art_free3_epi.
    split; [apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]|]. split; [apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]|].
    split; [apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]|]. split; [apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]|].
    split; [apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]|]. split; [apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]|].
    split; [apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]|]. split; [apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell]|].
    split; [apply T7_10; [clear; lia|clear; cbn; lia|apply TF; [clear; lia|clear; lia|exact F8]]|]. split; [apply T7_10; [clear; lia|clear; cbn; lia|apply TF; [clear; lia|clear; lia|exact F16]]|].
    split; [apply T7_10; [clear; lia|clear; cbn; lia|apply TF; [clear; lia|clear; lia|exact F24]]|]. split; [apply T7_10; [clear; lia|clear; cbn; lia|apply TF; [clear; lia|clear; lia|exact F32]]|].
    split; [apply T7_10; [clear; lia|clear; cbn; lia|apply TF; [clear; lia|clear; lia|exact F40]]|]. split; [apply T7_10; [clear; lia|clear; cbn; lia|apply TF; [clear; lia|clear; lia|exact F48]]|].
    apply T7_10; [clear; lia|clear; cbn; lia|apply TF; [clear; lia|clear; lia|exact F56]]. }
  (* [comment removed for export] *)
  assert (G010 : mem_grows M0 M10) by (eapply mem_grows_trans; [exact G08|exact G810]).
  assert (A68 : art_agree [(S - 4096, 4096); (p, 8); (S - 2272, 64); (2147450880 + 2 * q16, qr)] M6 M8).
  { pose proof (art_agree_trans _ _ _ _ _ A67 A78) as X. cbn [app] in X. exact X. }
  assert (A28 : art_agree [(S - 4096, 4096); (t + 3168, 1); (p - 16, 4); (p, 8); (t + 2824, 16); (2147450880 + 2 * q16, qr);
                           (0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23)] M2 M8).
  { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A23 (art_agree_trans _ _ _ _ _ A34 (art_agree_trans _ _ _ _ _ A45 (art_agree_trans _ _ _ _ _ A56 A68))))|].
    intros z. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. intros Hz Hout. cbn [art_out app fst snd] in Hout |- *. repeat split; lia. }
  assert (Cunw8 : cellA M8 (t + 3168) 1 0).
  { apply (art_cell_tr1 _ M6 M8 _ _ _ A68); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|]. apply (art_cell_tr1 _ M5 M6 _ _ _ A56); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|]. unfold M5, art_fx_fcu2_mem. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. zcell. }
  assert (OUT : art_free3_out M0 M10 S t p q16 qr l2 blk b1 n spb ris qs km L B cntB bszB bytes kb inited cl).
  { unfold art_free3_out. fold newb. rewrite <- ?Eb.
    split; [exact G010|].
    split.
    { intros x N1 N2. rewrite (AG810 x N2).
      destruct (Z.eq_dec (U x) (t + 3168)) as [e|ne].
      + assert (Ex : x = Z_to_bv 64 (t + 3168)) by (rewrite <- e; symmetry; apply Z_to_bv_bv_unsigned). rewrite Ex.
        rewrite (art_byte_of_cell1 M0 (t + 3168) 0 ltac:(clear - At_i; unfold apart in At_i; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear; lia) Cunw).
        apply art_byte_of_cell1; [clear - At_i; unfold apart in At_i; lia|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia|clear; lia|exact Cunw8].
      + apply A08. unfold art_free3_fp, dprivD in N1. cbn [art_out fst snd]. clear - N1 ne. repeat split; lia. }
    split.
    { apply (DInvD_frame l2 blk kb M6 M10 DI6). intros x Dx. rewrite (AG810 x (Z_dp _ Dx)). apply A68. revert Dx. apply art_dpriv_out; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t. }
    split.
    { apply (art_cell_agree _ M8 M10); [|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; cbn; lia|].
      - intros x Hx. apply AG810. apply HP24. clear - Hx. cbn in Hx. lia.
      - apply (art_cell_tr1 _ M6 M8 _ _ _ A68); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|]. apply (art_cell_tr1 _ M5 M6 _ _ _ A56); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|]. unfold M5, art_fx_fcu2_mem. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5. zcell. }
    split.
    { apply T810i; [clear; lia|clear; cbn; lia|]. apply (art_cell_tr1 _ M2 M8 _ _ _ A28); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zarith_t|exact Cia2]. }
    split.
    { intros k Hk. apply T810i; [clear - Hk; lia|clear - Hk; cbn; lia|]. apply (art_cell_tr1 _ M2 M8 _ _ _ A28); [revert Hk; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; intros Hk; zarith_t|exact (Ctab2 k Hk)]. }
    split; [exact PH10|]. split; [exact RC10|]. split; [exact OK10|]. split; [exact NEW10|]. split; [exact OLD10|exact Cby10]. }
  assert (W10 : wrA M10 (S - 4096) 4096) by (eapply wr_grows; [exact G010|exact W]).
  assert (E10_9 : getr r10 9 = Z_to_bv 64 (t + 80)).
  { rewrite K10 by inl. unfold r9; gres. rewrite P8_9. unfold r7; gres. reflexivity. }
  assert (E10_8 : getr r10 8 = Z_to_bv 64 0x13c8b0).
  { rewrite K10 by inl. unfold r9; gres. rewrite P8_8. unfold r7; gres. reflexivity. }
  assert (E10_22 : getr r10 22 = Z_to_bv 64 (2 ^ 20)).
  { rewrite K10 by inl. unfold r9; gres. apply KK8; [pk8|]. unfold r7; gres. reflexivity. }
  assert (KEPT : forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr r10 r = getr regs r).
  { intros r Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; rewrite K10 by inl; unfold r9; gres; (apply KK8; [pk8|]); unfold r7; gres; (apply KK6; [dk8|]); unfold r5; gres;
      try apply Z_to_bv_bv_unsigned; rewrite K4 by inl; first [ rewrite K3 by inl; rewrite K2 by inl; unfold r1; gres; reflexivity | rewrite Q3_4; symmetry; exact H4 ]. }
  assert (Hby'0 : 0 <= bytes' < 2 ^ 64). { rewrite Ebytes'. clear - Hby Hby' Hn. destruct newb; lia. }
  rewrite <- Ebytes' in Cby10.
  destruct (Z_le_gt_dec bytes' (2 ^ 20)) as [Hle|Hgt].
  - (* [comment removed for export] *)
    destruct EPI as (E36' & E44' & E52' & E60' & E68' & E76' & E84' & E92' & F8' & F16' & F24' & F32' & F40' & F48' & F56').
    pose proof (art_fx_fq2n_fn r10 M10 rom raw0 S p (t + 80) bytes' (U (getr regs 22)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
                 P10_2 E10_9 E10_22 Hret ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) HS47 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) (u64_range _) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - Hby'0 Hle; lia)
                 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
                 Cby10 E36' E44' E52' E60' E68' E76' E84' E92' F8' F16' F24' F32' F40' F48' F56') as RUN11.
    eapply ar_steps; [exact RUN11|]. apply ar_done.
    apply (KX1 _ M10).
    + gres. reflexivity.
    + gres. reflexivity.
    + intros r Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; try apply Z_to_bv_bv_unsigned; apply KEPT; inl.
    + exact Hle.
    + exact OUT.
  - (* [comment removed for export] *)
    pose proof (art_fx_fq2d_fn r10 M10 rom S (t + 80) 0x13c8b0 bytes' (t + 208) (S - 2128)
                 P10_2 E10_8 E10_9 E10_22 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) HS47 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; lia) ltac:(clear - Hby'0 Hgt; lia)
                 Cby10
                 ltac:(apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell])
                 ltac:(apply T7_10; [clear; lia|clear; cbn; lia|unfold M7, art_fx_fq1_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hkm Hkm' Htpd Htsdd Ec Eca Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs Hp Ep Hn Hqr HpHI Apt Apc Apl2 Apblk Apris Apfa Aps Hsh TR Hbot Hbt Htop4 Htop DG1 DG2 DG4 DG5; zcell])) as RUN11.
    eapply ar_steps; [exact RUN11|].
    apply (KX2 _ M10).
    + gres. bveq.
    + gres. exact P10_2.
    + gres. reflexivity.
    + gres. reflexivity.
    + gres. reflexivity.
    + gres. reflexivity.
    + intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; gres; apply KEPT; inl.
    + clear - Hgt. lia.
    + exact OUT.
    + exact EPI.
    + exact W10.
Qed.
End Spec.
