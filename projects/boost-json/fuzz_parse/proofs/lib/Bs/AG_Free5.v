(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AsDepotHash AsUnwind CidBits AW_AllocBase AW_MallocBase AW_IAInit AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AS_Free1 AS_Free2 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_RepQ.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_Free5 () := KReplay.lz_vm "#$8iC79OSSVerify6Proofs:boost_json:fuzz_parse3lib>AsanAllocModel7qc_listC13~~~I47Corelib4Init9Datatypes4!sJ#00K!sFA1K!tX^6qbatch01!tY%C46Stdlib5Lists4!s+#4last!ud_8qb_coun!ue&C5!t2&6ZArith6BinInt1Z3leb!v&25Logic2eq00C!s@73not!sv<2leK!su;1!su89False_ind!w:B2!tC<6leb_leC8!vNN2Bs<AG_Free!vO%need_new!y6Cbool!y6?!sF$1I!y6`cache00!tY&!z%f!sq&!yh_;kB!sq#C!yk,!uz,7Numbers7BinNums1Z01I!sD?0!z283and00!x5S8!tr$Rep4AREP!x,Cprod!tM#!}&55NoDup!{[#!sB52In!te\3alb!~H'!uk7iff!s?85proj1!tE\6ast_ok!tH&!sl[8inst_rep!snb9flags!sof:thread!spf7sec!smf6ia!sl-!#5n<t!ui]region!v[gpclas!wMgA!tb&shadow!swf?!sw&junk!suf4a_!#>%&!#5K^:ch!t^#!#>v+!{g]!sp%!uP,!td^5as_tq!t_b;!#8h#es!tamgq!sne;kNumC!zc#es!st%!#;E^5!w;$!#;D'!x&\placed!#6L[7!so$Wf2WF!sg&!#8>;2!v[_@as_internal_ini!#=>F2!uCP3Lib4TacX2b8!t'&!seS5Cells4cell04!vnV!tQ,wz!tQf3!vBC8positive02!sKG1!t\`2!uHf!#Ju&!#Ii;pow!sC=sub!wUUStep8rw_!tN#s!vo3!#B`13nat!vi?1N02I45stdpp9bitvector;def!{8#ions2bv00!vA`5!~ob5zbool!~&3!#D^$7!s+#Def6repeat!sE;3map!tN]a_ctx!|KZ2Nd;and_elimF17!sl]:!sl+4!z1CaddI!ww_!#7hY5ASegs5asegs!xab7AIAINIT!#35L3!t:\6AFLAGS!u$dC!smg<ASHBASE_CELL!wM_!so#ADOW_!st#!tcb;AHIGHMEMEND!sqb:ACANPOISON!y9eNITE!t_c8ACTXSIZE!sndTSD!zq7!#7761!wQ^ALLO!z%h6AHOOK!sleDYING!yxdREALMEMSET!y-d!smjGOT_LO!smb9!sm$VAL!#3fdPAGESZ!zedSECNAME!uNdPRIM!sof8ATLSSLO!wvc4!}6#!tZdLSANDI!wrc5!xc#2!skY9AW_IAInit8ia_after!soc;ia_pristine!srV!#?f3!#@S&!#59:6length!#gg<of_na!#k7_?compact_to_add!vA'!#b&6hd!#lH_pc!#lH/!#oy_b!tz/!sp^4zlen!t_fch_used!spe;!sp%r_beg!}~ca_sb!}6ca_th!w-'!zD24Znat5Nat2Z9is_nonnegC!#Lp?;bv_unsigned!yy+9micromega9SatDivModCZ_mod!sz&!t%'!{l<modulo!sF<>pow_pos!snC:!sN#!sJB7!|=$reK!u456VarMap1t01I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PExpr01K!stL!sQ75Tauto8G!sJ'5C!sJ<B!sJ&!sH6:Z!t<+=Z!sT$CheckerC!v#<4find!sqAC!sq0_sound!u9F4!u9<5eKind!#pr<unit!w:8!se%4kind!vd#!sf@1!#t[flas!#a}&!#_Y64True!#t;3!tX,:!zd%ison!z,8!w'-;!{G%!tv$!ur8!yc13Op203!sMI5!#3}R!#bN&8WF_!#yA#!#4lX!sm+co!#9hj6get_pc!soe9pc_!#f[#s!sre<ch!sr%!#8{\!$#1/6tq!$#/+!#>%_as!x-0!#=7_id!#[w%!$-9_!#sG$!#bB'!#>&^upd_nth!#<Ha3a_L!sieS!#>bdA!tU\!yQ%27free_s'!smY;AW_Enqueue29en!z@$_W!sr&!#UQ;app!#nJ78eq_ind_r!#F?7tlI!yZf!$-]&!w}]st!#aOW!#b;#Frame3iv!#fD%".
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~06qbatch37Corelib4Init9Datatypesk93nil37Corelib4Init5Logicm72eq07qc_listk94boolk94listk94truem73not37Corelib7Numbers7BinNumsq41Z0bkBatchCount04mkQB08qb_count06qcache79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAG_FreeModel~~~~~~u68need_new36Stdlib5Lists4Listhj34last46Stdlib6ZArith6BinInt1Zhke2le" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma need_new_true_full : ltac2:(zQ "h00!k1!m1!nb!o0!o9!p0!p7!pe!rd!s1!se!t4!te!hi8!hk6!hm6>1t$c>0@3$2$4@1$d^1$6>0@1$7@3$2@1$5$0@1$3^2@1$1$0@2$f$9@1$b@3$e$0@1$3^3@4$aZZZ@1$1$8").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_Free5 ()) ["HCW"] "##,ap'0h02NEh12NNh21mh31nh41Hh51bh61li001lh71rh81ti011qi021xp;1p;4p;3p;2g0000j17Tg001:R0j1?!s1$Zj19Tg002:j4<Tg003Ej32!s/$^j14Tg004ij26Tg005Fj30!s/$`j15Tg0069j21!s/$Uj2;!s/$oj2:Tg007Nj38!s/$nj2>Tg008Nj1=Tg009ZR1f0R2g00::R330p=3g00:Z%72g00;eR4#?R5P0P4!s&$1P2P3g00=0R0f2R6g00>>R7P7P7g00>\R7#9C<R8524#4R9'6n10110200020020!s4$0#3f1R:%94R;505#51109[[P2A0133A05;;#5A24;8#4,10P21;5;O1':W0W1A84:2=248#4,60#3A846:=05;#5g00?:16:2#3116:[R311:2166:#3R1[f3R9/16\11>:2P:n20010!s#$12!s-%0X27X37P3^27^37P2P0f4=849!t>%P6O3b4W0W1X75X54P:P2O2!uX%0!uX1b6%=2#3%7!ti&%76!u&&10[[eW8o"). Qed.

Section FreeNewHit.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.
  Let pc := get_pc st kBatchClass.
  Let cnt := pc_count pc.
  Let chunks := pc_chunks pc.
  Let cp := hd 0 chunks.
  Let B := compact_to_addr st kBatchClass cp.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x090c40 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  (* [comment removed for export] *)
  Let tq' := tq_new tq B (ch_chunk_beg ch) size.
  Let cache' := upd_nth (as_cache st) (zidx kBatchClass) (mkPC (cnt - 1) (tl chunks)).
  Let s' := free_s' s ch tq' cache' (a_L s) (a_S s) (a_AL s).
  (* [comment removed for export] *)
  Let Wh : list ivl := free_head_W lo (bv_unsigned sp) TH U size d.
  Let Wn : list ivl := enq_new_W lo (bv_unsigned sp) TH B LA.
  Let W : list ivl := Wh ++ Wn.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 32768.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis NN : need_new tq = true.
  Hypothesis HIT : cnt <> 0.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. ndestruct RR as (_ & _ & FL & _).
    ndestruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. ndestruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let HC24 : 0 <= kBatchClass < kNumClasses. Proof. unfold kBatchClass, kNumClasses. lia. Qed.
  Let PCS : pc_chunks (get_pc st kBatchClass) = cp :: tl chunks.
  Proof.
    pose proof (co_count _ _ (WF_cache st kBatchClass WFs HC24)) as C1. fold pc cnt chunks in C1.
    unfold cp. fold pc. fold chunks. destruct chunks as [|x r] eqn:E; [| reflexivity]. exfalso. apply HIT. rewrite C1. reflexivity.
  Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

End FreeNewHit.
End HCW.
(* [comment removed for export] *)
