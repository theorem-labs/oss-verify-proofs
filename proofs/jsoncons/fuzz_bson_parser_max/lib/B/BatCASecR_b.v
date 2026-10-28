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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatCachePop_b BatCombAlloc_b BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatSecAllocPost_b BatCASec_b BatSecRSpec_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_ca_sec_fp (sp t parr nch r msz : Z) (committed : bool) : list (Z * Z) :=
  (sp - 48, 48) :: art_sec_fp (sp - 48) t parr nch r msz committed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Theorem art_ca_sec_rspec_holds :
  forall (Q : list aev -> machine_state -> Prop) (P : Z -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
         (sp HI n q msz nm tp key tsd ctx t parr nch : Z) (committed : bool),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp ->
    getr regs 10 = Z_to_bv 64 1295832 -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 8 ->
    65536 < n < 2 ^ 40 -> n mod 8 = 0 -> 4096 * (q - 1) < n <= 4096 * q -> msz = 4096 * q + 4096 ->
    kHighMemBeg <= HI -> HI <= sp - 512 -> sp < 2 ^ 47 ->
    ((4096 <= t /\ t + 4096 <= 0x10000) \/ 0x696000 <= t) -> t + 4096 <= HI -> appmem t 4096 ->
    4096 <= ctx -> ctx + 4096 <= HI -> appmem ctx 4096 -> apart t 4096 ctx 4096 ->
    4096 <= tp - 88 -> tp < 0x696000 -> 4096 <= tsd -> tsd + 8 * key + 8 <= 0x696000 ->
    0x696000 <= parr -> parr mod 4096 = 0 -> parr + 2 ^ 23 <= HI -> appmem parr (2 ^ 23) -> apart parr (2 ^ 23) t 4096 ->
    0 <= nch < 16384 -> (committed = false -> nch = 0) -> 0x10000 <= nm < 2 ^ 47 ->
    wrA M (sp - 512) 512 -> wrA M t 4096 -> (committed = true -> wrA M parr 131072) ->
    cellA M 0x1374a0 8 0x1cf6e0 -> cellA M 0x1cf6e0 8 4096 -> cellA M (0x1d1768 + 260) 1 0 -> cellA M (0x1d1768 + 144) 8 0 ->
    cellA M 0x1374a8 8 0x139508 -> cellA M 0x139508 8 nm ->
    art_layout M -> art_tsd M tp key tsd ctx t ->
    cellA M 0x13c618 8 4096 -> cellA M (0x13c618 + 8) 8 parr -> cellA M (0x13c618 + 16) 8 parr -> cellA M (0x13c618 + 56) 8 nch ->
    cellA M (0x13c618 + 48) 8 (if committed then 16384 else 0) -> cellA M (0x13c618 + 616) 4 0 ->
    (forall Mx r, GR log Mx msz r -> P r) -> (forall r, P r -> art_sec_grant HI t ctx parr msz r) ->
    EVOK log (AMmapNull msz 0) ->
    (committed = false -> forall r, P r -> EVOK (log ++ [AMmapNull msz r]) (AMmapFixed (parr + 8 * nch) 131072)) ->
    (forall r regs' (M' : word -> option byte), P r ->
       getr regs' 10 = Z_to_bv 64 (4096 + r) -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
       (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
       mem_grows M M' -> art_agree (art_ca_sec_fp sp t parr nch r msz committed) M M' ->
       (forall (x : word) b, art_shlo r <= U x < art_shhi r msz -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> M x = Some b -> M' x = Some b) ->
       wrA M' r msz -> wrA M' (SB + r / 8) (msz / 8) ->
       cellA M' r 8 r -> cellA M' (r + 8) 8 msz -> cellA M' (r + 16) 8 n -> cellA M' (r + 24) 8 nch ->
       (forall x : word, r + 32 <= U x < r + msz -> M' x = Some (Z_to_bv 8 0)) ->
       cellA M' 0x13c618 8 4096 -> cellA M' (0x13c618 + 8) 8 parr -> cellA M' (0x13c618 + 16) 8 parr -> cellA M' (0x13c618 + 56) 8 (nch + 1) ->
       cellA M' (0x13c618 + 48) 8 16384 -> cellA M' (0x13c618 + 616) 4 0 ->
       cellA M' (parr + 8 * nch) 8 r -> wrA M' parr 131072 ->
       Q (log ++ art_sec_events msz r parr nch committed) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x56d3c : word) M rom).
Proof.
  intros Q P log regs M rom raw sp HI n q msz nm tp key tsd ctx t parr nch committed.
  intros H1 Hret H2 H4 H10 H12 H13 Hn Hn8 Hq Emsz.
  intros HHI Hs Hs' Ht Ht' APt Hctx Hctx' APc Atc Htp Htp' Htsd Htsd' Hparr Hparr4 Hparr' APp Apt Hnch Hnch0 Hnm.
  intros W Wt Wparr Cg28 Cpc Cfb C144 Cnm1 Cnm2 LAY TSD Cpg Cpab Cpab2 Cnch Cnres Clk HGR HP EV1 EV2 HK.
  pose proof HHI as HHI'. unfold kHighMemBeg in HHI'. subst raw.
  (* [comment removed for export] *)
  pose proof (art_ca_sec_pre_fn regs M rom sp 1295832 n H2 H10 H12 H13 ltac:(lia) ltac:(lia) Hn ltac:(lia) ltac:(lia)
                ltac:(eapply wr_sub; [exact W|lia|lia])) as RUN1.
  lazymatch type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (R1 := R) in RUN1; set (M1 := MM) in RUN1 end.
  eapply ar_steps; [exact RUN1|]. clear RUN1.
  assert (A01 : art_agree [(sp - 48, 48)] M M1).
  { unfold M1, art_ca_frame. eapply art_agree_sub; [zagree|]. clear - Hs Hs' HHI'. zsub. }
  assert (G01 : mem_grows M M1) by (unfold M1, art_ca_frame; zgrows).
  assert (TR : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k <= sp - 48 -> cellA M a k v -> cellA M1 a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr _ M M1 a k v A01); [|lia|lia|exact C]. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (AGimg : forall x : word, U x < 0x696000 -> M1 x = M x).
  { intros x Hx. apply (art_agree_pt _ _ _ x A01). cbn [art_out fst snd]. repeat split; try exact I; lia. }
  assert (AGctx : forall x : word, ctx + 152 <= U x < ctx + 160 -> M1 x = M x).
  { intros x Hx. apply (art_agree_pt _ _ _ x A01). cbn [art_out fst snd]. repeat split; try exact I; lia. }
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
  eapply (art_sec_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) P log R1 M1 rom (0x56de4 : bv 64)%bv (sp - 48) HI n q msz nm tp key tsd ctx t parr nch committed).
  all: try (unfold R1; gres; first [reflexivity | assumption]).
  all: try assumption.
  all: try lia.
  - unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
  - replace (sp - 48 - 464) with (sp - 512) by lia. eapply wr_grows; [exact G01|]. eapply wr_sub; [exact W|lia|lia].
  - eapply wr_grows; [exact G01|exact Wt].
  - intros E. eapply wr_grows; [exact G01|exact (Wparr E)].
  - apply TR; [lia|cbn; lia|exact Cg28].
  - apply TR; [lia|cbn; lia|exact Cpc].
  - apply TR; [lia|cbn; lia|exact Cfb].
  - apply TR; [lia|cbn; lia|exact C144].
  - apply TR; [lia|cbn; lia|exact Cnm1].
  - apply TR; [lia|cbn; lia|exact Cnm2].
  - apply (art_layout_agree M M1 AGimg LAY).
  - apply (art_tsd_agree M M1 tp key tsd ctx t AGimg AGctx Htp' Htsd' TSD).
  - apply TR; [lia|cbn; lia|exact Cpg].
  - apply TR; [lia|cbn; lia|exact Cpab].
  - apply TR; [lia|cbn; lia|exact Cpab2].
  - apply TR; [lia|cbn; lia|exact Cnch].
  - apply TR; [lia|cbn; lia|exact Cnres].
  - apply TR; [lia|cbn; lia|exact Clk].
  - (* [comment removed for export] *)
    intros r rS MS Pr S10 S2 S1 SK GS AS WIN WSr WSs Cr0 Cr8 Cr16 Cr24 ZB S0 S8 S16 S56 S48 S616 Sslot WSp.
    destruct (HP r Pr) as (Hr4 & Hr & Hri & Hrm & APr & Art & Arc & Arp).
    assert (Hm4 : msz mod 4096 = 0). { rewrite Emsz. replace (4096 * q + 4096) with ((q + 1) * 4096) by lia. apply Z_mod_mult. }
    destruct (art_sh_bounds r msz Hr4 Hm4 ltac:(lia) ltac:(lia) ltac:(lia)) as (SH1 & SH2 & SH3 & SH4 & _).
    unfold SB, kHighMemBeg in SH1, SH4.
    assert (GF : art_gap (art_sec_fp (sp - 48) t parr nch r msz committed) (sp - 48) 48).
    { clear - Hs Hs' HHI' Ht' Hrm SH1 SH4 Hparr' Hnch. unfold art_sec_fp. cbn [art_gap fst snd]. unfold apart. destruct committed; repeat split; try exact I; lia. }
    assert (FR : forall a (k : nat) v, sp - 48 <= a -> a + Z.of_nat k <= sp -> cellA M1 a k v -> cellA MS a k v).
    { intros a k v Ha Hk C. apply (art_cell_tr _ M1 MS a k v AS); [eapply art_gap_sub; [exact GF|lia|lia]|lia|lia|exact C]. }
    destruct (art_ca_sec_post rS MS rom (sp - 48) (getr regs 1) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)))
      as (rF & RUNF & F10 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & FK).
    + rewrite (SK 8%bv) by inl. unfold R1. gres. reflexivity.
    + exact S2.
    + lia.
    + lia.
    + apply FR; [lia|cbn; lia|]. unfold M1, art_ca_frame. replace (sp - 48 + 40) with (sp - 8) by lia. zcell.
    + exact Hret.
    + apply FR; [lia|cbn; lia|]. unfold M1, art_ca_frame. replace (sp - 48 + 32) with (sp - 16) by lia. zcell.
    + apply FR; [lia|cbn; lia|]. unfold M1, art_ca_frame. replace (sp - 48 + 24) with (sp - 24) by lia. zcell.
    + apply FR; [lia|cbn; lia|]. unfold M1, art_ca_frame. replace (sp - 48 + 16) with (sp - 32) by lia. zcell.
    + apply FR; [lia|cbn; lia|]. unfold M1, art_ca_frame. replace (sp - 48 + 8) with (sp - 40) by lia. zcell.
    + apply FR; [lia|cbn; lia|]. unfold M1, art_ca_frame. zcell.
    + eapply ar_steps; [exact RUNF|]. apply ar_done.
      apply (HK r rF MS Pr).
      * rewrite F10. exact S10.
      * rewrite F2. f_equal. lia.
      * exact F1.
      * intros x Hx. cbn [In] in Hx.
        destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
          first [ (rewrite F8; apply Z_to_bv_bv_unsigned) | (rewrite F9; apply Z_to_bv_bv_unsigned) | (rewrite F18; apply Z_to_bv_bv_unsigned)
                | (rewrite F19; apply Z_to_bv_bv_unsigned) | (rewrite F20; apply Z_to_bv_bv_unsigned)
                | (rewrite FK by (unfold art_pop_kept; repeat split; discriminate); rewrite SK by inl; unfold R1; gres; reflexivity) ].
      * eapply mem_grows_trans; [exact G01|exact GS].
      * unfold art_ca_sec_fp. exact (art_agree_trans _ _ _ _ _ A01 AS).
      * intros x b Hx Nx Mx. apply (WIN x b Hx Nx). rewrite (art_agree_pt _ _ _ x A01); [exact Mx|].
        clear - Hx SH4 Hs HHI'. cbn [art_out fst snd]. repeat split; try exact I; lia.
      * exact WSr. * exact WSs. * exact Cr0. * exact Cr8. * exact Cr16. * exact Cr24. * exact ZB.
      * exact S0. * exact S8. * exact S16. * exact S56. * exact S48. * exact S616. * exact Sslot. * exact WSp.
Qed.
End Spec.
