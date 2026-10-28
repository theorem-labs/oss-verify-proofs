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
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b
     BatCellEx_b BatCARSpec_b BatAlloc3Pure_b BatFxBatch1_b.
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
Definition art_enq_new_fp (sp t spb ris qs km b L B : Z) (x : Z) : Prop :=
  (sp - 64 <= x < sp) \/ art_refill_fp (sp - 64) t spb ris qs 24 km x \/ (t + 208 + 2576 <= x < t + 208 + 2584)
  \/ (b <= x < b + 32) \/ (L <> 0 /\ B <= x < B + 8) \/ (t + 80 <= x < t + 112 /\ (L <> 0 -> ~ (t + 88 <= x < t + 96))).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_enq_tail_W (t b L B : Z) : list (Z * Z) :=
  [ (t + 208 + 1920, 4); (t + 208 + 2576, 8); (b, 32); ((if L =? 0 then t + 80 + 8 else B), 8); (t + 80, 8); (t + 96, 16) ].

Lemma art_class_size_24 : AsanTab.class_size 24 = 8192. Proof. reflexivity. Qed.
Lemma art_ic_size_24 : art_ic_size 24 = 8192. Proof. reflexivity. Qed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_enq_finish :
  forall (Q : list aev -> machine_state -> Prop) (logE : list aev) regs rP (M MX rom : word -> option byte) (raw : word)
         (sp HI t qt spb ris qs km m n L B wB bytes sv : Z) (clp : art_cls) (FP0 : Z -> Prop),
    let c := t + 80 in
    let ca := t + 208 in
    let cnt := Z.of_nat (length (cl_cache clp)) in
    let w := last (cl_cache clp) 0 in
    let b := spb + 24 * 2 ^ 32 + 16 * w in
    ret_ok raw -> HI <= sp - 736 -> sp < 2 ^ 47 ->
    spb = 65536 * qs -> 0x10007fff8000 <= spb -> ris = spb + 2 ^ 37 -> ris + 4096 <= HI -> 4096 <= t -> t + 4096 <= HI -> t = 4096 * qt ->
    apart t 4096 spb (2 ^ 37 + 4096) -> apart t 4096 0x10000 (0x696000 - 0x10000) ->
    cl_cache clp <> [] -> art_cls_ok 24 clp ->
    0 <= L < 2 ^ 63 -> 0 <= B < 2 ^ 63 -> 0 <= bytes -> bytes + n + 8192 < 2 ^ 64 -> 0 <= n -> 0 <= m < 2 ^ 64 -> 0 <= sv < 2 ^ 64 ->
    (L <> 0 -> B = spb + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au clp) wB /\ wB <> w) ->
    mem_grows M MX -> (forall x : word, ~ FP0 (U x) -> MX x = M x) ->
    art_pc_hdr ca true MX -> art_cls_rep ca spb ris 24 clp MX -> wrA MX t 4096 ->
    cellA MX (ca + 2576) 8 sv -> cellA MX 0x13c5f8 8 spb ->
    cellA MX c 8 L -> cellA MX (c + 24) 8 bytes -> (L <> 0 -> cellA MX (c + 16) 8 B) ->
    cellA MX (sp - 8) 8 (U raw) -> cellA MX (sp - 16) 8 (U (getr regs 8)) -> cellA MX (sp - 24) 8 (U (getr regs 9)) -> cellA MX (sp - 32) 8 (U (getr regs 18)) ->
    cellA MX (sp - 40) 8 (U (getr regs 19)) -> cellA MX (sp - 48) 8 (U (getr regs 20)) -> cellA MX (sp - 56) 8 (U (getr regs 21)) ->
    getr rP 2 = Z_to_bv 64 (sp - 64) -> getr rP 10 = Z_to_bv 64 c -> getr rP 11 = Z_to_bv 64 ca -> getr rP 13 = Z_to_bv 64 m -> getr rP 14 = Z_to_bv 64 n ->
    getr rP 15 = Z_to_bv 64 cnt ->
    (forall x : reg, In x [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr rP x = getr regs x) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        mem_grows M M' ->
        (forall x : word, ~ FP0 (U x) -> art_out (art_enq_tail_W t b L B) (U x) -> M' x = M x) ->
        mem_grows MX M' -> art_agree (art_enq_tail_W t b L B) MX M' ->
        art_pc_hdr ca true M' -> art_cls_rep ca spb ris 24 (art_cls_pop clp) M' ->
        cellA M' b 8 0 -> cellA M' (b + 8) 8 (n + 8192) -> cellA M' (b + 16) 8 1 -> cellA M' (b + 24) 8 m ->
        cellA M' c 8 (L + 1) -> cellA M' (c + 16) 8 b -> cellA M' (c + 24) 8 (bytes + (n + 8192)) ->
        (L = 0 -> cellA M' (c + 8) 8 b) -> (L <> 0 -> cellA M' B 8 b) ->
        Q logE (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q logE (mkst rP (0x56b98 : word) MX rom).
Proof.
  intros Q logE regs rP M MX rom raw sp HI t qt spb ris qs km m n L B wB bytes sv clp FP0 c ca cnt w b
         Hret HHI Hsp' Espb Hspb Eris Hris Ht Ht' Et Atk Ati Hne OK HL HB0 Hby Hby' Hn Hm Hsv HB GX AX PH CR Wt Csv Cspb CL Cby CB
         F1 F8 F9 F18 F19 F20 F21 P2 P10 P11 P13 P14 P15 KP K.
  assert (Ec : c = t + 80) by reflexivity. assert (Eca : ca = t + 208) by reflexivity. assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * w) by reflexivity.
  clearbody c ca b.
  pose proof Atk as Xk. unfold apart in Xk. pose proof Ati as Xi. unfold apart in Xi.
  pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
  rewrite art_class_size_24 in Hfor.
  assert (Hcnt : 1 <= cnt <= 16). { unfold cnt. destruct (cl_cache clp); [contradiction|]. cbn [length] in *. lia. }
  assert (Hch : art_cptr_ok 8192 (cl_au clp) w).
  { apply (proj1 (Forall_forall _ _) Hfor). apply in_or_app. left. unfold w. rewrite (app_removelast_last 0 Hne) at 2. apply in_or_app. right. left. reflexivity. }
  pose proof Hch as (Hw0 & Hw1 & _).
  destruct CR as [[C0 CW] RR]. pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _ & _ & _ & _ & Wu).
  destruct (PH 24 ltac:(lia)) as [_ Pcsz]. cbn [andb] in Pcsz. rewrite art_ic_size_24 in Pcsz.
  assert (HBf : L <> 0 -> 0 <= wB /\ 16 * wB + 8192 <= cl_au clp /\ (16 * wB + 8192 <= 16 * w \/ 16 * w + 8192 <= 16 * wB)).
  { intros NL. destruct (HB NL) as (_ & (Hb0 & Hb1 & (iB & EiB)) & Nw). destruct Hch as (_ & _ & (iw & Eiw)). repeat split; [exact Hb0|exact Hb1|]. clear - EiB Eiw Nw. lia. }
  assert (Wc : wrA MX c 32) by (eapply wr_sub; [exact Wt|lia|lia]).
  assert (Wb : wrA MX b 32) by (eapply wr_sub; [exact Wu|lia|lia]).
  assert (RUN : msteps ASEGS (mkst rP (0x56b98 : word) MX rom)
            (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd rP 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 (U (getr regs 8)))) 9 (Z_to_bv 64 (U (getr regs 9)))) 11 (Z_to_bv 64 (bytes + (n + 8192)))) 12 (Z_to_bv 64 (L + 1))) 14 (Z_to_bv 64 (n + 8192))) 15 (Z_to_bv 64 L)) 16 (Z_to_bv 64 103079215104)) 18 (Z_to_bv 64 (U (getr regs 18)))) 19 (Z_to_bv 64 (U (getr regs 19)))) 20 (Z_to_bv 64 (U (getr regs 20)))) 21 (Z_to_bv 64 (U (getr regs 21))))
                  raw (art_enq_new_mem MX c ca L B bytes b m n cnt sv) rom)).
  { rewrite Eb.
    apply (art_enq_new_tail_fn rP MX rom raw sp c ca spb L B bytes w m n cnt sv (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)));
      first [ assumption | apply u64_range | idtac ].
    all: try (intros NL; destruct (HB NL) as (EB & _ & _); destruct (HBf NL) as (HB1 & HB2 & HB3)).
    all: try (unfold apart; lia).
    - rewrite Eca, Et. replace (4096 * qt + 208 + 2576) with ((512 * qt + 348) * 8) by lia. apply Z_mod_mult.
    - eapply wr_sub; [exact Wt|lia|lia].
    - eapply wr_sub; [exact Wt|lia|lia].
    - rewrite <- Eb. exact Wb.
    - eapply wr_sub; [exact Wu|lia|lia].
    - unfold w. rewrite art_last_nth. replace (ca + 1936 + 4 * (cnt - 1)) with (ca + 80 * 24 + 16 + 4 * Z.of_nat (length (cl_cache clp) - 1)) by (unfold cnt; lia). apply CW. lia.
    - replace (ca + 1928) with (ca + 80 * 24 + 8) by lia. exact Pcsz. }
  eapply ar_steps; [exact RUN|]. apply ar_done. clear RUN.
  set (a8 := if L =? 0 then t + 80 + 8 else B).
  assert (Fa8 : (a8 = c + 8 /\ L = 0) \/ (a8 = B /\ L <> 0 /\ spb + 24 * 2 ^ 32 <= a8 /\ a8 + 8192 <= spb + 24 * 2 ^ 32 + cl_au clp /\ (a8 + 8192 <= b \/ b + 8192 <= a8))).
  { unfold a8. destruct (Z.eqb_spec L 0) as [EL|NL]; [left; split; [lia|exact EL]|right]. destruct (HB NL) as (EB & _ & _). destruct (HBf NL) as (HB1 & HB2 & HB3). repeat split; lia. }
  assert (EM2 : art_enq_new_mem MX c ca L B bytes b m n cnt sv
                = Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 MX (ca + 1920) (cnt - 1)) (ca + 2576) (sv + 8192)) b 0) (b + 8) (n + 8192)) (b + 16) 1) (b + 24) m) a8 b) c (L + 1)) (c + 16) b) (c + 24) (bytes + (n + 8192))).
  { unfold art_enq_new_mem, a8. rewrite Ec. reflexivity. }
  rewrite EM2. clear EM2.
  assert (EW : art_enq_tail_W t b L B = [ (t + 208 + 1920, 4); (t + 208 + 2576, 8); (b, 32); (a8, 8); (t + 80, 8); (t + 96, 16) ]) by reflexivity.
  rewrite EW in K. clear EW. clearbody a8.
  set (M2 := Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 MX (ca + 1920) (cnt - 1)) (ca + 2576) (sv + 8192)) b 0) (b + 8) (n + 8192)) (b + 16) 1) (b + 24) m) a8 b) c (L + 1)) (c + 16) b) (c + 24) (bytes + (n + 8192))).
  assert (A2 : art_agree [ (t + 208 + 1920, 4); (t + 208 + 2576, 8); (b, 32); (a8, 8); (t + 80, 8); (t + 96, 16) ] MX M2).
  { unfold M2. eapply art_agree_sub; [zagree|]. intros z Hz Hout. cbn [art_out app fst snd] in Hout |- *. clear - Hout Ec Eca. repeat split; lia. }
  assert (G2 : mem_grows MX M2) by (unfold M2; zgrows).
  apply (K _ M2).
  - gres. reflexivity.
  - gres. reflexivity.
  - intros r Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; first [apply Z_to_bv_bv_unsigned | apply KP; inl].
  - eapply mem_grows_trans; [exact GX|exact G2].
  - intros x N Hout. rewrite (A2 x Hout). apply AX. exact N.
  - exact G2.
  - exact A2.
  - (* [comment removed for export] *)
    apply (art_pc_hdr_tr _ ca true MX M2 ltac:(lia) ltac:(lia) A2); [|exact PH]. intros c' Hc'. revert Hc'; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; intros Hc'. zarith_t.
  - (* [comment removed for export] *)
    split.
    + split.
      * cbn [art_cls_pop cl_cache]. rewrite art_removelast_length by exact Hne.
        replace (Z.of_nat (length (cl_cache clp) - 1)) with (cnt - 1) by (unfold cnt; lia). replace (ca + 80 * 24) with (ca + 1920) by lia. unfold M2.
        do 9 (apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|lia|cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|]).
        apply cell_Wn_hit; [lia|cbn; lia].
      * cbn [art_cls_pop cl_cache]. intros j Hj. rewrite art_removelast_length in Hj by exact Hne. rewrite art_removelast_nth by exact Hj.
        apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|apply CW; lia]. revert Hj Hl16; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; intros Hj Hl16. zarith_t.
    + apply (art_region_rep_upd spb ris 24 0 0 clp (art_cls_pop clp) MX M2 [ (t + 208 + 1920, 4); (t + 208 + 2576, 8); (b, 32); (a8, 8); (t + 80, 8); (t + 96, 16) ]); try reflexivity;
        first [ lia | exact RR | exact G2 | exact A2 | (intros; reflexivity) | idtac ].
      * clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
      * clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
      * cbn [art_cls_pop cl_free]. clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
      * apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rmx]. clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
      * apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rnf]. clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
      * apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rna]. clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
  - unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
  - unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
  - unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
  - unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
  - unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
  - unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
  - unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
  - intros EL. assert (E8 : a8 = c + 8) by (clear - EL Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia). rewrite <- E8. unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
  - intros NL. assert (E8 : a8 = B) by (clear - NL Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia). rewrite <- E8. unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
Qed.

#[using="Type"] Lemma art_last_in : forall l : list Z, l <> [] -> In (last l 0) l.
Proof. intros l H. rewrite (app_removelast_last 0 H) at 2. apply in_or_app. right. left. reflexivity. Qed.

#[using="Type"] Lemma art_refill_au_mono : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl -> cl_au cl <= cl_au (art_cls_refill c cl).
Proof.
  intros c cl Hc OK. rewrite art_cls_refill_eq. cbn [art_cls_take cl_au]. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl); [|lia].
  cbn [art_cls_populate cl_au]. destruct OK as (_ & (Hau0 & Haumu) & _). pose proof (art_class_size_facts c Hc) as (Hsz & _).
  assert (0 <= art_cls_new c cl) by (unfold art_cls_new; apply Z.div_pos; lia). nia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_refill_fp_out64 : forall sp HI t spb ris qs km x, HI <= sp - 736 -> sp < 2 ^ 47 -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> ris = spb + 2 ^ 37 -> ris + 4096 <= HI ->
  4096 <= t -> t + 4096 <= HI -> apart t 4096 spb (2 ^ 37 + 4096) -> apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> apart t 4096 0x10000 (0x696000 - 0x10000) ->
  0 <= km -> 262144 * km <= 3758096384 ->
  (sp - 64 <= x < sp) \/ (t + 208 + 2576 <= x < t + 208 + 2584) \/ (t + 80 <= x < t + 112) \/ (0x10000 <= x < 0x696000) -> ~ art_refill_fp (sp - 64) t spb ris qs 24 km x.
Proof.
  intros sp HI t spb ris qs km x HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Ati Hkm Hkm' Hx F. unfold art_refill_fp in F. unfold apart in Atk, Ats, Ati.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]; try lia. destruct F as (c' & Hc' & F). lia.
Qed.

#[using="Type"] Theorem art_enq_new_aruns :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
         (sp HI t ctx tp key tsd spb ris qs km st m n L B wB bytes : Z) (inited : bool) (cl : art_cls),
    let c := t + 80 in
    let ca := t + 208 in
    let b := spb + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl in
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp ->
    getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 n ->
    HI <= sp - 736 -> sp < 2 ^ 47 -> art_geo HI t ctx tp tsd spb ris qs ->
    wrA M (sp - 736) 736 -> wrA M t 4096 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    art_pc_hdr ca inited M -> art_cls_rep ca spb ris 24 cl M -> art_cls_ok 24 cl -> (cl_cache cl <> [] -> inited = true) -> cl_mu cl = 262144 * km ->
    (cl_cache cl = [] -> art_cls_needs_populate 24 cl = true ->
       cl_mu cl + 262144 <= 3758096384
       /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new 24 cl) <= 536870912
       /\ wrA M (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 32768 * km) 32768
       /\ wrA M (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 469762048) 67108864) ->
    art_evok_list EVOK log (art_ca_events spb 24 cl) ->
    (* [comment removed for export] *)
    0 <= L < 2 ^ 63 -> 0 <= B < 2 ^ 63 -> 0 <= bytes -> bytes + n + 8192 < 2 ^ 64 -> 0 <= n -> 0 <= m < 2 ^ 64 ->
    cellA M c 8 L -> cellA M (c + 24) 8 bytes ->
    (L <> 0 -> B = spb + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au cl) wB /\ ~ In wB (cl_cache cl ++ cl_free cl)
               /\ cellA M (c + 16) 8 B /\ cellA M (B + 16) 8 1021) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        mem_grows M M' ->
        (forall x : word, ~ art_enq_new_fp sp t spb ris qs km b L B (U x) -> M' x = M x) ->
        art_pc_hdr ca true M' -> art_cls_rep ca spb ris 24 (art_cls_pop (art_ca_pre 24 cl)) M' -> art_cls_ok 24 (art_cls_pop (art_ca_pre 24 cl)) ->
        art_cptr_ok 8192 (cl_au (art_ca_pre 24 cl)) (art_ca_cptr 24 cl) ->
        (cl_cache cl = [] -> art_cls_needs_populate 24 cl = true ->
           forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 32768 * km + j) 1 250) ->
        cellA M' b 8 0 -> cellA M' (b + 8) 8 (n + 8192) -> cellA M' (b + 16) 8 1 -> cellA M' (b + 24) 8 m ->
        cellA M' c 8 (L + 1) -> cellA M' (c + 16) 8 b -> cellA M' (c + 24) 8 (bytes + (n + 8192)) ->
        (L = 0 -> cellA M' (c + 8) 8 b) -> (L <> 0 -> cellA M' B 8 b) ->
        Q (log ++ art_ca_events spb 24 cl) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x56b58 : word) M rom).
Proof.
  intros Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs km st m n L B wB bytes inited cl c ca b
         H1 Hret H2 H4 H10 H11 H12 H13 H14 HHI Hsp' GEO W Wt PC LY T PH RC OK Hin Emu Room EV HL HB0 Hby Hby' Hn Hm CL Cby HB K.
  assert (Hc : 1 <= 24 <= 30) by lia.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  clear G9 G10 G15 G16.
  pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _). rewrite art_class_size_24 in Hfor.
  assert (Hkm : 0 <= km) by lia.
  assert (Ec : c = t + 80) by reflexivity. assert (Eca : ca = t + 208) by reflexivity. assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl) by reflexivity.
  clearbody c ca b.
  pose proof G11 as X11. unfold apart in X11. pose proof At_i as Xi. unfold apart in Xi. pose proof At_s as Xs. unfold apart in Xs.
  assert (HBf : L <> 0 -> spb + 24 * 2 ^ 32 <= B /\ B + 8192 <= spb + 24 * 2 ^ 32 + cl_au cl).
  { intros NL. destruct (HB NL) as (EB & (Hb0 & Hb1 & _) & _). lia. }
  (* [comment removed for export] *)
  destruct (art_enq_new_head regs M rom raw sp c L B H1 H2 H10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HL ltac:(lia) ltac:(lia)
              ltac:(unfold apart; lia) ltac:(intros NL; destruct (HBf NL); unfold apart; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) CL
              ltac:(intros NL; destruct (HB NL) as (_ & _ & _ & X1 & X2); split; assumption)) as (r1 & RUN1 & R1_2 & K1).
  set (M1 := art_enq_frame M sp raw regs) in *.
  assert (A1 : art_agree [(sp - 64, 64)] M M1). { unfold M1, art_enq_frame. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G1' : mem_grows M M1) by (unfold M1, art_enq_frame; zgrows).
  assert (FC : cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
               /\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (sp - 48) 8 (U (getr regs 20)) /\ cellA M1 (sp - 56) 8 (U (getr regs 21))).
  { unfold M1, art_enq_frame. repeat split; zcell. }
  destruct FC as (FC1 & FC8 & FC9 & FC18 & FC19 & FC20 & FC21).
  eapply ar_steps; [exact RUN1|].
  (* [comment removed for export] *)
  destruct RC as [CR RR].
  assert (PH1 : art_pc_hdr ca inited M1).
  { apply (art_pc_hdr_tr _ ca inited M M1 ltac:(lia) ltac:(lia) A1); [|exact PH]. intros c' Hc'. clear - Hc' Eca HHI G7 G8. zarith_t. }
  assert (CR1 : art_cache_rep ca 24 (cl_cache cl) M1).
  { apply (art_cache_rep_tr _ ca 24 (cl_cache cl) M M1 ltac:(lia) ltac:(lia) ltac:(lia) Hl16 A1); [| |exact CR]; clear - Eca HHI G7 G8; zarith_t. }
  assert (RR1 : art_region_rep spb ris 24 0 cl M1).
  { pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
    apply (art_region_rep_upd spb ris 24 0 0 cl cl M M1 [(sp - 64, 64)]); try reflexivity;
      first [ lia | exact RR | exact G1' | exact A1 | (intros; reflexivity) | idtac ].
    - clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t.
    - clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t.
    - clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hnf4 Hmfa1. zarith_t.
    - apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rmx]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t.
    - apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rnf]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t.
    - apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rna]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t. }
  assert (PC1 : art_prim_consts spb ris M1). { eapply art_prim_consts_fp; [exact A1| |exact PC]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
  assert (Wt1 : wrA M1 t 4096) by (eapply wr_grows; [exact G1'|exact Wt]).
  assert (TC1 : forall a v, t + 80 <= a -> a + 8 <= t + 112 -> cellA M a 8 v -> cellA M1 a 8 v).
  { intros a v Ha Ha' C. apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact C]. clear - Ha Ha' HHI Hsp' G7 G8. zarith_t. }
  assert (CL1 : cellA M1 c 8 L) by (apply TC1; [lia|lia|exact CL]).
  assert (Cby1 : cellA M1 (c + 24) 8 bytes) by (apply TC1; [lia|lia|exact Cby]).
  assert (CB1 : L <> 0 -> cellA M1 (c + 16) 8 B) by (intros NL; destruct (HB NL) as (_ & _ & _ & X1 & _); apply TC1; [lia|lia|exact X1]).
  assert (R1K : forall r : reg, In r [1; 3; 4; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r) by exact K1.
  assert (Hcase : cl_cache cl = [] \/ cl_cache cl <> []) by (destruct (cl_cache cl); [left; reflexivity|right; discriminate]).
  destruct Hcase as [Ecache|Hne].
  2:{ (* [comment removed for export] *)
    assert (Epre : art_ca_pre 24 cl = cl) by (unfold art_ca_pre; destruct (cl_cache cl); [contradiction|reflexivity]).
    assert (Eev : art_ca_events spb 24 cl = []) by (unfold art_ca_events; destruct (cl_cache cl); [contradiction|reflexivity]).
    rewrite Eev in K. rewrite app_nil_r in K. unfold art_ca_cptr in Eb. rewrite Epre in K, Eb.
    pose proof (Hin Hne) as ->.
    set (cnt := Z.of_nat (length (cl_cache cl))).
    assert (Hcnt : 1 <= cnt <= 16). { unfold cnt. destruct (cl_cache cl); [contradiction|]. cbn [length] in *. lia. }
    destruct (art_tcell_exists M1 t 2784 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (sv & Hsv & Csv).
    pose proof CR1 as [C0 CW]. pose proof PC1 as (Pspb & _).
    pose proof (art_enq_new_pop_fn r1 M1 rom ca cnt ltac:(rewrite R1K by inl; exact H11) ltac:(lia) ltac:(lia) Hcnt ltac:(replace (ca + 1920) with (ca + 80 * 24) by lia; exact C0)) as RUN2.
    eapply ar_steps; [exact RUN2|]. subst c ca.
    apply (art_enq_finish Q log regs (regupd r1 15 (Z_to_bv 64 cnt)) M M1 rom raw sp HI t qt spb ris qs km m n L B wB bytes sv cl (fun x => sp - 64 <= x < sp)
             Hret HHI Hsp' Espb G4 Eris G6 G7 G8 Et G11 At_i Hne OK HL HB0 Hby Hby' Hn Hm Hsv).
    + intros NL. destruct (HB NL) as (EB & CPB & NIB & _). split; [exact EB|]. split; [exact CPB|]. intros E. apply NIB. apply in_or_app. left. rewrite E.
      rewrite (app_removelast_last 0 Hne) at 2. apply in_or_app. right. left. reflexivity.
    + exact G1'.
    + intros x N. apply A1. cbn. split; [clear - N; lia|exact I].
    + exact PH1.
    + split; [exact CR1|exact RR1].
    + exact Wt1.
    + replace (t + 208 + 2576) with (t + 2784) by lia. exact Csv.
    + exact Pspb.
    + exact CL1.
    + exact Cby1.
    + exact CB1.
    + exact FC1.
    + exact FC8.
    + exact FC9.
    + exact FC18.
    + exact FC19.
    + exact FC20.
    + exact FC21.
    + gres. exact R1_2.
    + gres. rewrite R1K by inl. exact H10.
    + gres. rewrite R1K by inl. exact H11.
    + gres. rewrite R1K by inl. exact H13.
    + gres. rewrite R1K by inl. exact H14.
    + gres. reflexivity.
    + intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; gres; apply R1K; inl.
    + intros regs' M' S2 S1 SK SG SA SGX SAX SPH SCR B1 B2 B3 B4 L1 L2 L3 LE LN. rewrite <- Eb in *.
      apply (K regs' M' S2 S1 SK SG); try assumption.
      * intros x N. apply SA.
        -- intros F. apply N. left. exact F.
        -- unfold art_enq_tail_W. cbn [art_out fst snd]. unfold art_enq_new_fp, art_refill_fp in N.
           repeat match goal with H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H end.
           destruct (Z.eqb_spec L 0) as [EL|NL]; repeat split; lia.
      * apply art_cls_ok_pop; assumption.
      * unfold art_ca_cptr. rewrite ?Epre. apply (proj1 (Forall_forall _ _) Hfor). apply in_or_app. left. apply art_last_in. exact Hne.
      * intros E. contradiction. }
  (* [comment removed for export] *)
  assert (Epre : art_ca_pre 24 cl = art_cls_refill 24 cl) by (unfold art_ca_pre; rewrite Ecache; reflexivity).
  assert (Eev : art_ca_events spb 24 cl = art_refill_events spb 24 cl) by (unfold art_ca_events; rewrite Ecache; reflexivity).
  rewrite Eev in EV, K. unfold art_ca_cptr in Eb.
  pose proof (art_ca_cptr_origin 24 cl Hc OK) as ORG. unfold art_ca_cptr in ORG. rewrite Epre in K, Eb, ORG.
  pose proof CR1 as [C0 _]. rewrite Ecache in C0. cbn in C0.
  pose proof (art_enq_new_ra_fn r1 M1 rom c ca st m n ltac:(rewrite R1K by inl; exact H10) ltac:(rewrite R1K by inl; exact H11) ltac:(rewrite R1K by inl; exact H12)
                ltac:(rewrite R1K by inl; exact H13) ltac:(rewrite R1K by inl; exact H14) ltac:(lia) ltac:(lia)
                ltac:(replace (ca + 1920) with (ca + 80 * 24) by lia; exact C0)) as RUN3.
  match type of RUN3 with msteps _ _ (mkst ?R _ _ _) => set (r3 := R) in RUN3 end.
  eapply ar_steps; [exact RUN3|].
  assert (L1 : art_layout M1). { eapply art_layout_fp; [exact A1| |exact LY]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
  assert (T1 : art_tsd M1 tp key tsd ctx t).
  { eapply art_tsd_fp; [exact A1| | |exact G19|exact G20|exact G21|exact G22|exact T].
    - intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia.
    - intros z Hz. cbn. clear - Hz HHI G1 G13 G14. repeat split; lia. }
  destruct (art_tcell_exists M1 t 2872 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (m1 & _ & Cm1).
  destruct (art_tcell_exists M1 t 2880 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (m2 & _ & Cm2).
  destruct (art_tcell_exists M1 t 2792 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (sv0 & _ & Csv0).
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st0 H; exact H].
  apply (art_refill_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r3 M1 rom (0x56cac : bv 64)%bv (sp - 64) HI t ctx tp key tsd spb ris qs 24 km inited cl
           ltac:(unfold r3; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold r3; gres; exact R1_2) ltac:(unfold r3; gres; rewrite R1K by inl; exact H4)
           ltac:(unfold r3; gres; rewrite Eca; reflexivity) ltac:(unfold r3; gres; rewrite Eca; f_equal; lia) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
           Hc ltac:(lia) ltac:(lia) GEO ltac:(eapply wr_grows; [exact G1'|]; eapply wr_sub; [exact W|lia|lia]) Wt1 PC1 L1 T1
           ltac:(rewrite <- Eca; exact PH1) ltac:(rewrite <- Eca; exact (conj CR1 RR1)) OK Ecache Emu
           ltac:(exists m1, m2, sv0; repeat split; [exact Cm1|exact Cm2|replace (t + 208 + 2584) with (t + 2792) by lia; exact Csv0])
           ltac:(intros NP; destruct (Room Ecache NP) as (Q1 & Q2 & Q3 & Q4); repeat split; first [assumption | eapply wr_grows; [exact G1'|assumption]]) EV).
  intros rR MR R10 R2 R1 RK RG RA RPH RCR ROK RSH.
  set (clr := art_cls_refill 24 cl) in *. set (nr := art_refill_n 24).
  pose proof (art_pre_take_enough 24 cl Hc OK) as Hen. fold nr in Hen.
  destruct (art_refill_need 24 Hc) as (_ & Hnr). fold nr in Hnr.
  assert (Lc : length (cl_cache clr) = nr). { unfold clr. rewrite art_cls_refill_eq. fold nr. cbn [art_cls_take cl_cache]. rewrite length_skipn. lia. }
  assert (Hne' : cl_cache clr <> []). { intros E. rewrite E in Lc. cbn in Lc. lia. }
  pose proof RCR as [[D0 DW] DRR]. rewrite Lc in D0.
  assert (WtR : wrA MR t 4096) by (eapply wr_grows; [exact RG|exact Wt1]).
  assert (OUT : forall x, (sp - 64 <= x < sp) \/ (t + 208 + 2576 <= x < t + 208 + 2584) \/ (t + 80 <= x < t + 112) \/ (0x10000 <= x < 0x696000) -> ~ art_refill_fp (sp - 64) t spb ris qs 24 km x).
  { intros x Hx. exact (art_refill_fp_out64 sp HI t spb ris qs km x HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_s At_i Hkm ltac:(lia) Hx). }
  assert (TR : forall a (k : nat) v, ((sp - 64 <= a /\ a + Z.of_nat k <= sp) \/ (t + 80 <= a /\ a + Z.of_nat k <= t + 112) \/ (0x10000 <= a /\ a + Z.of_nat k <= 0x696000)) ->
                 cellA M1 a k v -> cellA MR a k v).
  { intros a k v Ha C. apply (art_cell_agree _ M1 MR); [|clear - Ha HHI G1 G7; lia|clear - Ha Hsp' G7 G8 HHI; lia|exact C]. intros x Hx. apply RA. apply OUT. clear - Ha Hx. lia. }
  pose proof (art_enq_new_rb_fn rR MR rom c ca st m n (Z.of_nat nr) R10
                ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity)
                ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (ca + 1920) with (t + 208 + 80 * 24) by lia; exact D0)) as RUN4.
  eapply ar_steps; [exact RUN4|].
  destruct (art_tcell_exists MR t 2784 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) WtR) as (sv & Hsv & Csv).
  pose proof ROK as (_ & (Hau0r & Haumur) & _ & _ & _ & Hmu3r & _ & (_ & Hmfa1r) & Hnf4r & Hforr & _). rewrite art_class_size_24 in Hforr.
  pose proof (art_refill_au_mono 24 cl Hc OK) as Haum. fold clr in Haum.
  replace (Z.of_nat nr) with (Z.of_nat (length (cl_cache clr))) by (rewrite Lc; reflexivity).
  subst c ca.
  apply (art_enq_finish Q (log ++ art_refill_events spb 24 cl) regs _ M MR rom raw sp HI t qt spb ris qs km m n L B wB bytes sv clr
           (fun x => (sp - 64 <= x < sp) \/ art_refill_fp (sp - 64) t spb ris qs 24 km x)
           Hret HHI Hsp' Espb G4 Eris G6 G7 G8 Et G11 At_i Hne' ROK HL HB0 Hby Hby' Hn Hm Hsv).
  + intros NL. destruct (HB NL) as (EB & CPB & NIB & _). split; [exact EB|]. split; [eapply art_cptr_mono; [exact Haum|exact CPB]|].
    intros E. destruct ORG as [ORG|(_ & _ & ORG)]; [apply NIB; rewrite E; exact ORG|]. destruct CPB as (_ & CPB1 & _). rewrite <- E in ORG. clear - ORG CPB1. lia.
  + eapply mem_grows_trans; [exact G1'|exact RG].
  + intros x N. rewrite (RA x) by (intros F; apply N; right; exact F). apply A1. cbn. split; [|exact I]. intros F. apply N. left. clear - F. lia.
  + exact RPH.
  + exact RCR.
  + exact WtR.
  + replace (t + 208 + 2576) with (t + 2784) by lia. exact Csv.
  + pose proof PC1 as (Pspb & _). apply TR; [right; right; cbn; lia|exact Pspb].
  + apply TR; [right; left; cbn; lia|exact CL1].
  + apply TR; [right; left; cbn; lia|exact Cby1].
  + intros NL. apply TR; [right; left; cbn; lia|exact (CB1 NL)].
  + apply TR; [left; cbn; lia|exact FC1].
  + apply TR; [left; cbn; lia|exact FC8].
  + apply TR; [left; cbn; lia|exact FC9].
  + apply TR; [left; cbn; lia|exact FC18].
  + apply TR; [left; cbn; lia|exact FC19].
  + apply TR; [left; cbn; lia|exact FC20].
  + apply TR; [left; cbn; lia|exact FC21].
  + gres. exact R2.
  + gres. reflexivity.
  + gres. reflexivity.
  + gres. reflexivity.
  + gres. reflexivity.
  + gres. reflexivity.
  + intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; gres; rewrite RK by inl; unfold r3; gres; apply R1K; inl.
  + intros regs' M' S2 S1 SK SG SA SGX SAX SPH SCR B1 B2 B3 B4 L1' L2 L3 LE LN. rewrite <- Eb in *.
    apply (K regs' M' S2 S1 SK SG); try assumption.
    * intros x N. apply SA.
      -- intros [F|F]; apply N; [left; exact F|right; left; exact F].
      -- unfold art_enq_tail_W. cbn [art_out fst snd]. unfold art_enq_new_fp, art_refill_fp in N.
         repeat match goal with H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H end.
         destruct (Z.eqb_spec L 0) as [EL|NL]; repeat split; lia.
    * apply art_cls_ok_pop; assumption.
    * unfold art_ca_cptr. rewrite ?Epre. apply (proj1 (Forall_forall _ _) Hforr). apply in_or_app. left. apply art_last_in. exact Hne'.
    * intros _ NP j Hj. pose proof (RSH NP j Hj) as C.
      apply (art_cell_tr1 _ MR M' _ _ _ SAX); [|exact C].
      assert (Fa8 : L = 0 \/ (spb + 24 * 2 ^ 32 <= B /\ B + 8192 <= spb + 24 * 2 ^ 32 + cl_au cl)) by (destruct (Z.eq_dec L 0) as [EL|NL]; [left; exact EL|right; exact (HBf NL)]).
      assert (Hw : 0 <= last (cl_cache clr) 0 /\ 16 * last (cl_cache clr) 0 + 8192 <= cl_au clr).
      { pose proof (proj1 (Forall_forall _ _) Hforr (last (cl_cache clr) 0) ltac:(apply in_or_app; left; apply art_last_in; exact Hne')) as (X0 & X1 & _). split; assumption. }
      unfold art_enq_tail_W. clear - Hj Xs X11 Fa8 Hw Eb G4 Espb Hkm Emu Hmu3 G6 Eris G2 G7 G8 HHI Hsp' Haumu Haumur Hmu3r Hau0.
      destruct (Z.eqb_spec L 0) as [EL|NL]; zarith_t.
Qed.
End Spec.
