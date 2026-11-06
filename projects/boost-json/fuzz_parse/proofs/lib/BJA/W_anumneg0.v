(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0 AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import BJRep AXpres AKitChk AKitCells AKitIn AKitRV AKitSeg W_anum0.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import N8Store.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~m03mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~q34cellk14consq32C8q32C1q32C4q32CBk13nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hg75asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hkb8rw_cellshfbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hq03le4k13appk16option01Z3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehv3h0le_bytes_to_word" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs; try transport_cond_ro segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition nframe : ltac2:(zQ "40!h9!jc!l9!pd>1m$3>3sp'@1$1@1$0#k0>2j8@1$2@1$1@1$0#8>4mant@1$1@1$0#k0>4bias@1$1@1$0#k0>4expo@1$1@1$0#k0>4xneg@1$1@1$0#8>3neg@1$1@1$0#8>2j6@1$2@1$1@1$0#8>4slot@1$1@1$0#k0>3s5v@1$1@1$0#k0>3s4v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s0v@1$1@1$0#k0>3rav@1$1@1$0#k0P") := ltac2:(zQ "e0!h9!tf!jc!u6!ud!l9!v2!v7!vc!hg1!hk2!pd!ho6!hp2\1m$b\3sp'@1$2@1$0#k0\2j8@1$5@1$2@1$0#8\4mant@1$2@1$0#k0\4bias@1$2@1$0#k0\4expo@1$2@1$0#k0\4xneg@1$2@1$0#8\3neg@1$2@1$0#8\2j6@1$5@1$2@1$0#8\4slot@1$2@1$0#k0\3s5v@1$2@1$0#k0\3s4v@1$2@1$0#k0\3s3v@1$2@1$0#k0\3s2v@1$2@1$0#k0\3s1v@1$2@1$0#k0\3s0v@1$2@1$0#k0\3rav@1$2@1$0#k0@4$c$a^h1@2$d@1$0#k0^h0@3$3$1@2$8N8^f@3$3$1@1$4^e@3$3$1@1$7^d@3$3$1@1$7^c@3$3$1@1$6^b@3$3$1@1$6^a@3$3$1@2$8N6^9@3$3$1@1$4^8@3$3$1@1$4^7@3$3$1@1$4^6@3$3$1@1$4^5@3$3$1@1$4^4@3$3$1@1$4^3@3$3$1@1$4^2@3$3$1@1$4^1@1$9$1").
  Definition nctx {HCEIL : HeapCeil} (sp' pa : word) (lo e : Z) : Prop :=
    aceil <= lo /\ lo + 48 <= bv_unsigned sp' /\ bv_unsigned sp' + 96 <= 2^47 /\ aapp (bv_unsigned pa) 280 /\ bv_unsigned pa mod 16 = 0 /\ 0 <= e <= aceil.
  Ltac open_nctx UX := box_post; destruct UX as (CEIL & ROOM & SPT & APP & PA16 & EHI).
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- uregs _ _ _ _ _ => unfold uregs
    | |- uframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold uframe
    | |- nframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold nframe
    | |- ucells _ _ _ _ => unfold ucells
    end.
  Ltac useg_begin r ::=
    intro_rv r; subst; unfold uframe, nframe, uvs in *; unfold seg_post, uregs, uframe, nframe, ucells, uvs; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ ?s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ s0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    acb;
    try (lazymatch goal with APP : aapp _ 280 |- _ =>
           pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5); unfold AIMG_TOP in APB1; unfold AAPP_HI in APB3 end);
    shad_bounds.
  (* [comment removed for export] *)
  Lemma nframe_merge8 : ltac2:(zQ "h10!tf!u6!ud!h9!jc!v2!vc!l9!hg1!hk2!v7!hta!ho6!hu1!hu7!hv0!ii2>1m>0@1$4@1$3#k0@1$e@1$4@1$3#8>1A$f>2j8@1$7@1$4@1$3#8>2mw@1$4@1$3#k0>1b@1$4@1$3#k0>1x@1$4@1$3#k0>2xg@1$4@1$3#8>2ng@1$4@1$3#8>2j6@1$7@1$4@1$3#8>2sl@1$4@1$3#k0>3s5v@1$4@1$3#k0>3s4v@1$4@1$3#k0>3s3v@1$4@1$3#k0>3s2v@1$4@1$3#k0>3s1v@1$4@1$3#k0>3s0v@1$4@1$3#k0>3rav@1$4@1$3#k0>0@4$c$9^h1^h0@3$1$0@2$6N8^f@3$1$0@1$2^e@3$1$0@1$a^d@3$1$0@1$a^c@3$1$0@1$5^b@3$1$0@1$5^a@3$1$0@2$6N6^9@3$1$0@1$2^8@3$1$0@1$2^7@3$1$0@1$2^6@3$1$0@1$2^5@3$1$0@1$2^4@3$1$0@1$2^3@3$1$0@1$2^2@3$1$0@1$2^1@1$8$0@4$c$9^h2^h1@3$1$0@2$6N8^h0@3$1$0@1$2^f@3$1$0@1$2@1$h0@3$d@1$4@1$3#8@1$b^e@1$b^d@3$1$0@1$5^c@3$1$0@1$5^b@3$1$0@2$6N6^a@3$1$0@1$2^9@3$1$0@1$2^8@3$1$0@1$2^7@3$1$0@1$2^6@3$1$0@1$2^5@3$1$0@1$2^4@3$1$0@1$2^3@3$1$0@1$2^2@1$8$0").
  Proof.
    intros until rav. intros R. pose proof R as [[W _] _]. cbn in W.
    eapply rw_cells_rebytes; [exact R| | | reflexivity].
    - cbn. tauto.
    - cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by (rewrite length_app, !length_le4; reflexivity). rewrite <- ?app_assoc. reflexivity.
  Qed.
  Ltac merge8 ::=
    match goal with
    | UF : rw_cells _ ?m ?A [C8 _; C4 _; C4 _; C1 _; C1 _; CB 6 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        apply uframe_merge8 in UF
    | UF : rw_cells _ ?m ?A [CB 8 _; C8 _; C4 _; C4 _; C1 _; C1 _; CB 6 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        apply nframe_merge8 in UF
    end.

(* [comment removed for export] *)
Ltac chkjoin2 t back :=
  pose_reg_shb; norm_s32;
  lazymatch goal with
  | |- evt ?segs _ (MS ?R ?F _ ?fc ?oe ?m ?rom) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 t)) in
      let Rf := constr:(fun tv : word => ltac:(let r := eval cbv beta iota delta [tset] in (@tset word p tv R) in exact r)) in
      eapply (evt_cut segs (fun ms => exists tv : word, ms = MS (Rf tv) F (Z_to_bv 64 back) fc oe m rom));
      [ st1b; norm_lits; norm_s32;
        let K := fresh "K" in if_cases K; zify_cond K; try rewrite !unsigned_zb in K; box_ugly K;
        [ (* [comment removed for export] *) apply evt_done; cbv beta; eexists; reflexivity
        | (* [comment removed for export] *)
          first [ exfalso; clear - K; lia | idtac ];
          st1b; norm_lits; st1b; norm_lits; norm_s32; st1b; norm_lits; norm_s32;
          let K2 := fresh "K" in if_cases K2; zify_cond K2; try rewrite !unsigned_zb in K2; box_ugly K2;
          [ exfalso; unbox_shad_for K2; lia
          | st1b; norm_lits; apply evt_done; cbv beta; eexists; reflexivity ] ]
      | cbv beta; let ms1 := fresh "ms" in let tv := fresh "jt" in intros ms1 (tv & ->); clear_shb_facts ]
  end.

(* [comment removed for export] *)
Ltac achk ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 1061564 => chkjoin2 11 1061572   (* [comment removed for export] *)
    | 1061608 => chkjoin2 11 1061616   (* [comment removed for export] *)
    | 1061644 => chkjoin2 13 1061652   (* [comment removed for export] *)
    | 1061704 => chkjoin2 11 1061712   (* [comment removed for export] *)
    | 1061832 => chkjoin 7 1061836   (* [comment removed for export] *)
    | 1061948 => chkjoin 6 1061952   (* [comment removed for export] *)
    | 1062052 => chkjoin2 13 1062060   (* [comment removed for export] *)
    | 1062104 => chkjoin 13 1062108   (* [comment removed for export] *)
    | 1062184 => chkjoin2 12 1062192   (* [comment removed for export] *)
    | 1062236 => chkjoin2 12 1062244   (* [comment removed for export] *)
    | 1062332 => chkjoin 12 1062336   (* [comment removed for export] *)
    | 1062380 => chkjoin2 12 1062388   (* [comment removed for export] *)
    | 1062460 => chkjoin 12 1062464   (* [comment removed for export] *)
    | 1062540 => chkjoin 5 1062544   (* [comment removed for export] *)
    | 1062640 => chkjoin 12 1062644   (* [comment removed for export] *)
    | 1063096 => chkjoin 14 1063100   (* [comment removed for export] *)
    | 1063232 => chkjoin 12 1063236   (* [comment removed for export] *)
    | 1063296 => chkjoin 14 1063300   (* [comment removed for export] *)
    | 1063340 => chkjoin 12 1063344   (* [comment removed for export] *)
    | 1063400 => chkjoin 14 1063404   (* [comment removed for export] *)
    | 1063464 => chkjoin 14 1063468   (* [comment removed for export] *)
    | 1063508 => chkjoin 12 1063512   (* [comment removed for export] *)
    | 1063552 => chkjoin 14 1063556   (* [comment removed for export] *)
    | 1063596 => chkjoin 12 1063600   (* [comment removed for export] *)
    | 1063640 => chkjoin 14 1063644   (* [comment removed for export] *)
    | 1063692 => chkjoin 13 1063696   (* [comment removed for export] *)
    | 1063736 => chkjoin 12 1063740   (* [comment removed for export] *)
    | 1063780 => chkjoin 14 1063784   (* [comment removed for export] *)
    | 1063824 => chkjoin 12 1063828   (* [comment removed for export] *)
    | 1063868 => chkjoin 14 1063872   (* [comment removed for export] *)
    | 1063912 => chkjoin 12 1063916   (* [comment removed for export] *)
    | 1063956 => chkjoin 14 1063960   (* [comment removed for export] *)
    | 1064000 => chkjoin 12 1064004   (* [comment removed for export] *)
    | 1064044 => chkjoin 14 1064048   (* [comment removed for export] *)
    | 1064144 => chkjoin 12 1064148   (* [comment removed for export] *)
    | 1064196 => chkjoin 12 1064200   (* [comment removed for export] *)
    | 1064224 => chkjoin 12 1064228   (* [comment removed for export] *)
    | 1064276 => chkjoin 12 1064280   (* [comment removed for export] *)
    | 1064320 => chkjoin 14 1064324   (* [comment removed for export] *)
    | 1064376 => chkjoin 12 1064380   (* [comment removed for export] *)
    | 1064444 => chkjoin 13 1064448   (* [comment removed for export] *)
    | 1064496 => chkjoin 14 1064500   (* [comment removed for export] *)
    | 1064540 => chkjoin 12 1064544   (* [comment removed for export] *)
    | 1064660 => chkjoin 14 1064664   (* [comment removed for export] *)
    | 1064704 => chkjoin 12 1064708   (* [comment removed for export] *)
    | 1064748 => chkjoin 14 1064752   (* [comment removed for export] *)
    | 1064792 => chkjoin 12 1064796   (* [comment removed for export] *)
    | 1064836 => chkjoin 14 1064840   (* [comment removed for export] *)
    | 1064880 => chkjoin 12 1064884   (* [comment removed for export] *)
    | 1064944 => chkjoin 5 1064948   (* [comment removed for export] *)
    | 1064972 => chkjoin 28 1064976   (* [comment removed for export] *)
    | 1064996 => chkjoin 29 1065000   (* [comment removed for export] *)
    | 1065020 => chkjoin 29 1065024   (* [comment removed for export] *)
    | 1065172 => chkjoin 15 1065176   (* [comment removed for export] *)
    | 1065192 => chkjoin 15 1065196   (* [comment removed for export] *)
    | 1065224 => chkjoin 15 1065228   (* [comment removed for export] *)
    | 1065244 => chkjoin 16 1065248   (* [comment removed for export] *)
    | 1065268 => chkjoin 16 1065272   (* [comment removed for export] *)
    | 1065356 => chkjoin 14 1065360   (* [comment removed for export] *)
    | 1065408 => chkjoin 12 1065412   (* [comment removed for export] *)
    | 1065484 => chkjoin 17 1065488   (* [comment removed for export] *)
    | 1065616 => chkjoin 6 1065620   (* [comment removed for export] *)
    | 1065644 => chkjoin 29 1065648   (* [comment removed for export] *)
    | 1065668 => chkjoin 30 1065672   (* [comment removed for export] *)
    | 1065692 => chkjoin 30 1065696   (* [comment removed for export] *)
    | 1065848 => chkjoin 15 1065852   (* [comment removed for export] *)
    | 1065900 => chkjoin 16 1065904   (* [comment removed for export] *)
    | 1065920 => chkjoin 16 1065924   (* [comment removed for export] *)
    | 1065964 => chkjoin 12 1065968   (* [comment removed for export] *)
    | 1066028 => chkjoin 16 1066032   (* [comment removed for export] *)
    | 1066048 => chkjoin 17 1066052   (* [comment removed for export] *)
    | 1066072 => chkjoin 17 1066076   (* [comment removed for export] *)
    | 1066148 => chkjoin 11 1066152   (* [comment removed for export] *)
    | 1066408 => chkjoin 12 1066412   (* [comment removed for export] *)
    | 1066456 => chkjoin 11 1066460   (* [comment removed for export] *)
    | 1066496 => chkjoin 13 1066500   (* [comment removed for export] *)
    | 1066536 => chkjoin 12 1066540   (* [comment removed for export] *)
    end
  end.
(* [comment removed for export] *)
