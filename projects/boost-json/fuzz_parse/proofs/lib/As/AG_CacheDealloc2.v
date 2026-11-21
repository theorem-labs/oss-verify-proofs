(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach AllocSim MmapSim LazyRestrict LazyLedger AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require LazyMadvise.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepX
     AW_Efs AS_Rta AG_Refill3 AG_RepQ.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_CacheDealloc2 () := KReplay.lz_vm "#$jQC46Stdlib9micromega5Tauto5eKindK!sE;8GFormula08K47Corelib4Init9Datatypes4list01I!sFA0!t266VarMap1t02I!sD?0!sD6=RingM!s4'7!tu'0!tu,7Numbers7BinNums1Z02!tS67Env!sr#5PExpr01!sIE2!t2=8positive!sn#!sKE2!vs<6option!u$8!uq:1!xS<8B!sJ&!t=25Logic2eq!sb8:Z!t2+=Z!sn$CheckerI!sl;0C!x4<4find!t3AC!t30_soundC5!sX&6ZArith6BinInt1Z2le!tU83and00!s]>tC89OSSVerify6Proofs:boost_json:fuzz_parse3lib2As7AG_RepQ:WFQ_regionC13~~~!|CF4!sJF5I!zp?0!xnD3Op203!}4=uni!}49!tW%4kind!zl/!sf81I!x%@;!w,%!vl$!}9?!{`,3!}^@1!ulI5!ul=bool!tX/!sF81C7!xzN>AsanAllocModel;kNumClasses!y#%!ypS8!ss$Rep4a_sb!sj&!zx;3add!t/UsShadow5aceil!ttepa!ttB6modulo!tw\4aapp!tvb5a_thr!skdkobj!tXectx!skef!y4+!yx_t!sj&!{Z^6as_sec!so&!}Z'5Lists4!s+#2In!t-_:sc_map_beg!t{e;!ss&size!|kCmul!vz]dis!y@'!#:17not!{3`op!u5Cpow!t0_bot!yvb2RB!shcFA!u\Csub!sC=div!#=pT!tJ#Wf8ro_fa_le!z2e:get!#>c/!ss_<rg_num_freed!sueDrg!{v#ped!sx$_array!w|Y!vX'9!vX%mod!sna;ro!u`#!u_j=rg!uX5!sv^4zlen!uWa=ro!wB'!vK,!ta^>!x:,user!z&fas_space!#6zh:!{j%!ss-!~vXKit=!sp,_eq!ss&!#6e68eq_ind_r!u-_?!yN,_base!u3bB!su2!u8,!vz_class!#:u-!ss^9max_coun!#8PY6AS_Rta7rta_mf!#DM%!#P/8or!#NW=7div!|%$!sG;=mod_pos_b!#O~?!sM$neg!sM25!#JS#8PreO!s/#1Z;!t>#0_r_ext!sL>!st#!sL3!u14compare!#L@?3!#VU=3Pol!#N@=3nat!#U^E5Psatz!sO8!#Nh:3!#X:D4!um<8leb_spec!#=&<leb!#N`;8BoolSpec00C!sJ;6length!t/34Znat5Nat2Z9is_nonneg!#KY<of_nat!v^K7!#]>?!#P@P8HeapCeil5h!#N>^!#M2%2sh!shb;!#Om#_fact!#QiY9!#3@#RepX@sh_!st#ing_rang!#4:%K!#Z3;1!wh<>pow!~9$!x8B:!sN#!sJ%!|z>N!#`tF7!#=_ZF!#6{+_table!vl\3Lib2Nd:and_elimF6!skg4!wM'!{TI4!sOK6!#3]M2!#gQA2!|q@3!#^rE7!xPE5!sIE3!usK5!taF3!v?N!#]uI1!~G\6AHI_LO!#?RekSpaceS!#?RhkPag!srj@kPtrArrayReserv!#C0_Rep8AFS_SIZE!#@P%!ti^6schunk00!u\eAkFree!u]$Map!vXi<kUser!sul@!tq,Offset!#D17!~a,:!#Ad$ison!#ev=!#A&#1!#Dv75False00!sC84True00!xu\6AMODEL!#;cb7akernel!snd!t]%X!{Cb?amaps_in_ledger!suds!#3l#_visibl!}1c7ABUDGET!zJe7as_!u`#!spfmp_kin!#TX%K!sp^5m!#po#3!spl4!|o'5stdpp9bitvector;definitions2bv!|04!#<u,prod00!v?c!#S#,!t[@7Z_to_bv!t>c!#RP+K!uPA1C4ELinuxProcessSemantics?!s<25State8m_vm!yN$!s]P7vm!z+$!#{U9x00!v5A;bv_unsigned!tHQ;vm_noac!s;#!},\3a_L!|7V<LazyRestrict:in!#Is$!#n_'!sqO:!sq#L!#4@#9nooverlap!sna>entries_nowr!ss+!v{Tr!#?:$d!#QP;3fst!sC=sn!x?R8vm_limit!s]Q9a!x:#!#m7#!xt[4a_Z!#8^V3Lib4TacX2wz!#;+b4hc!#\mZ!sk/!#tG+!sk^!#fh[6SecGap4zsum!sh&!#Xf<tb!xWQ=!#=V#subtractK!#6F_apping01!u]Y!#3E-S!}baD!uK0!}h1!tdR:!$0r#fill3I!#4A+!t&,fal!#fJZ!t%-H!t%7tru!t$eJ!t$7insid!#zXB6ltb_lt!#j075proj2!#4U<app!sC=orb!#}w'4Bool!s'$:orb!ui$!#k,Q!#9+/>!ud-!$'u+!#LA^as_ptr!#rN/!vO<shiftl!$$K6:in!t^#_iff!#c|=t!#c|$!$;Q8or02!wR86!#n\$!s\<1!s\89!#LZ#!s_#!uF=eq_dec!#?k16Specif7sum!$4x%!v}^6!#q9$!#39'!z&<!#WWS;!t3$Budget6pusag!#E#'!#Xo39SatDivModCZ_div!#a@%!#akB8sub_diag!tj_;!tj%_grow!#66a4aPhi!{YV!#BV0eager_us!#{uW!sq0;pages_tota!$8/eAL!}5B!#rF#pos!u#^win_n!u+$Z!usc9cl!#s/$s!spc5cl_lo!slg!y4+!#BmR6M!#>j#<!#Jr&_lit!|\I!#v2#!|\0!u8\@!ye-_con!vwd?!sw/!$=s[!#Ci+D!#nv,lt_!#dW/!#>Yqkeep!x:Z9LiaTuning9zify_don!#`:V;!vh#MadviseI!$&#%!$#y#!#BY/!trZ!#n6/3!sk];!sk+18!slh!tZ'!#H1O<map!zo#tains!#;%+!#>]$7!s+#Def3map!#P\Q!w<-!#?Z66filter!#mwE6I!#Imf!#hc%!sr_!#\v%!sp&!#]he!#uO%!$N'A2!w?QBtarget_!#S%$!#Sc$!#@+^B_PRIM!v\e!#B'&0!#4wb6schigh!wLl2!spl8!uQY5ASegs8AIMG_TOP!#5EU!t]2;kR!w2$!#oO,!#@iS!#vO%9ALOWSH!#8y[!uR%7!uR$!sj[!#WM,AHC0!skfL!skd7ASECMAX!wse7PROT_RW!spe>!xe-Lo!$>~&!#6z58ni!#@2%!#_\Ppage!#h[#!#O47!#t1$1".
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~07AMODELX79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~k89placed_ok46Stdlib6ZArith6BinInt1Zp22le37Corelib4Init5Logicqf3and69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~s9ekFreeArraySizek83a_L69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~hi1eentries_nowrapk84a_AL" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section CDModel.
  Variables (s : ast) (mo mo' : Model) (XC XB : list Z) (c : Z) (st' : astate) (L' S' : list (word * word)) (AL2 k mfa' : Z) (fl' : list Z).
  Let st := a_st s.
  Let sb := a_sb s.
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r.
  Let nf' := nf + k.
  Let s2 := mkAst st' (a_thr s) (a_ctx s) (a_fsb s) L' S' (a_Zr s) AL2 (a_top s) (a_bot s).
  Let h := m_vmmaps mo.
  Let h' := m_vmmaps mo'.

  Hypothesis AMX : ltac2:(zQ "10!jf@3$0?5HCEIL?1s?2mo").
  Hypothesis PL : ltac2:(zQ "10!o6@2$0?5HCEIL?1s").
  Hypothesis WQ : WFQ st XC XB.
  Hypothesis HC : ltac2:(zQ "20!qa!s3@2$1@2$0+1?1c@2$0?1c+he").
  (* [comment removed for export] *)
  Hypothesis KR : (k = 0 /\ mfa' = mfa) \/ (k = max_count c / 2 /\ mfa' = rta_mfa nf k mfa).
  Hypothesis FROOM : ltac2:(zQ "20!hga!qa@2$1?4mfa'$0").
  (* [comment removed for export] *)
  Hypothesis Fsb : as_space_beg st' = as_space_beg st. Hypothesis Fpa : as_ptr_array st' = as_ptr_array st.
  Hypothesis Fsec : as_sec st' = as_sec st.
  Hypothesis Frg_c : get_region st' c = mkRegion mu au nf' fl' mfa'.
  Hypothesis Frg_o : forall c0, 0 <= c0 -> c0 <> c -> get_region st' c0 = get_region st c0.
  Hypothesis Fmaps : as_maps st' = (if mfa <? mfa' then [mkMap (FA s c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false] else []) ++ as_maps st.
  Hypothesis LNW : ltac2:(zQ "20!hhb!hle@1$1@1$0?1s").
  (* [comment removed for export] *)
  Hypothesis EL : L' = (if mfa <? mfa' then maps_subtract (a_L s) (FA s c + mfa) (FA s c + mfa') else a_L s).
  Hypothesis ES : S' = (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else []) ++ a_S s.
  Hypothesis VMM : vm_maps h' = vm_maps h.
  Hypothesis VMR : vm_reserved h' = vm_reserved h.
  Hypothesis VML : vm_limit h' = vm_limit h.
  Hypothesis VMB : vm_mmap_base h' = vm_mmap_base h.
  Hypothesis VMT : alloc_top h' = alloc_top h.
  Hypothesis VMN : vm_noaccess h' = (if mfa <? mfa' then maps_subtract (vm_noaccess h) (FA s c + mfa) (FA s c + mfa') else vm_noaccess h).
  Hypothesis EAG : eager_used mo' <= eager_used mo + (mfa' - mfa).
  Hypothesis HAL : ltac2:(zQ "30!qa!s3!hn0@2$1@2$0Z?3AL2@2$0?3AL2@1$2?1s").

  Let RO : region_ok st c. Proof. exact (WFQ_region st _ _ c WQ ltac:(clear - HC; unfold kNumClasses; lia)). Qed.

  Let B : 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384
          /\ 0 <= mfa /\ mfa <= mfa' <= 536870912 /\ 1 <= c <= 30
          /\ 8 * ((mfa' - mfa) / 8) = mfa' - mfa /\ (FA s c + mfa) mod 8 = 0 /\ mfa mod 262144 = 0 /\ (mfa' - mfa) mod 262144 = 0 /\ mfa' <= mfa + 262144
          /\ mu mod 262144 = 0.
  Proof.
    clear AMX Fsb Fpa Fsec Frg_c Frg_o Fmaps LNW EL ES VMM VMR VML VMB VMT VMN EAG HAL.
    npose PL as (Y1 & Y2 & Y3 & _). fold sb in Y1, Y2, Y3.
    pose proof (ro_fa_le _ _ RO) as F1. pose proof (ro_fa_mod _ _ RO) as F2. pose proof (ro_numfreed _ _ RO) as F3. pose proof (ro_mapped_mod _ _ RO) as F4.
    fold st r nf mfa mu in F1, F2, F3, F4. unfold zlen in F3.
    assert (ERB : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    assert (EFA : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    npose (class_size_table_facts c ltac:(clear - HC; lia)) as (_ & _ & _ & C4 & C5 & C6).
    unfold AHI_LO, kSpaceSize, kPageSize, kFreeArraySize, kFreeArrayMapSize, kUserMapSize in *.
    assert (M : mfa <= mfa' /\ (mfa' - mfa) mod 262144 = 0 /\ mfa' <= mfa + 262144).
    { destruct KR as [(_ & ->)|(-> & ->)]; [clear; Z.div_mod_to_equations; lia|].
      unfold rta_mfa, efs_new, round_up, kFreeArrayMapSize. destruct (Z.leb_spec (4 * (nf + max_count c / 2)) mfa) as [LE|GT]; [clear; Z.div_mod_to_equations; lia|].
      clear - GT F1 F2 F3 C4 C5 C6. Z.div_mod_to_equations. lia. }
    clear - Y1 Y2 Y3 ERB EFA F1 F2 F3 F4 M FROOM HC. acb. Z.div_mod_to_equations. repeat split; lia.
  Qed.

  Theorem amodelx_after_cd : AMODELX s2 mo'.
Proof.
  (* LPS revision repair (75d69e00, checker 2c6b6db8), rule 11g, same cure as As//Bs
     AG_Refill3.v.  The replay that stood here rebuilt amaps_in_ledger's OLD first conjunct:
     the farm's error was its reconstructed term "has type ... In (Z_to_bv 64 (mp_base mp),
     Z_to_bv 64 (mp_size mp)) (vm_maps (m_vmmaps mo')) /\ 0 <= mp_base mp < 2 ^ 64 ...
     while it is expected to have type amaps_in_ledger s2 mo'".  The STATEMENT above is
     unchanged; only the proof moves, written out rather than re-encoded.
     DONOR: a donor tree:projects/openssl/echconfiglist_parser/proofs/lib/As/
     AG_CacheDealloc2.v lines 83-174 -- the same Section CDModel, whose preamble diffs against
     this one only in the five encoded hypotheses (AMX, PL, HC, FROOM, LNW, HAL) and in B's
     two npose/pose-proof lines.  As in AG_Refill3, the donor tree still carries the OLD
     amaps_in_ledger and its text ports unchanged, because the one consumer of IL1 is
     `exact (IL1 mp Hin' K1' K2' K3' K4')` and the restatement puts the guard on the goal and
     on IL1 in the same position.  This transition does not touch vm_maps either
     (VMM : vm_maps h' = vm_maps h).
     The text is character-identical on the As and Bs sides. *)
    destruct AMX as [[AIL [ASV ABU]] [AK AKR]]. pose proof B as (B1 & B2 & ERB & EFA & B5 & B6 & B7 & M1 & M2 & M3 & M4 & M5 & M6).
    assert (NUM := conj B1 (conj B2 (conj ERB (conj EFA (conj B5 (conj B6 (conj B7 M5))))))).
    destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    pose proof AK as (K1 & K2 & K3 & K4a & K4b & K4c & K5a & K5b & K5c & K6a & K6b & K7 & K8a & K8b & K8c & K9 & K10 & K11).   (* [comment removed for export] *)
    set (subF := fun X : list (word * word) => if mfa <? mfa' then maps_subtract X (FA s c + mfa) (FA s c + mfa') else X).
    assert (ELs : L' = subF (a_L s)) by (rewrite EL; subst subF; reflexivity).
    assert (ENs : vm_noaccess h' = subF (vm_noaccess h)) by (rewrite VMN; subst subF; reflexivity).
    assert (NWF : forall X, entries_nowrap X -> entries_nowrap (subF X)).
    { intros X HX. subst subF. destruct (mfa <? mfa'); [apply maps_subtract_nowrap; [exact HX| clear - NUM; lia| clear - NUM; lia]| exact HX]. }
    assert (SUBf : forall X x, entries_nowrap X -> in_rangesb x X = false -> in_rangesb x (subF X) = false).
    { intros X x HX F. subst subF. destruct (mfa <? mfa'); [| exact F].
      apply in_rangesb_subtract_false; [exact HX| clear - NUM; lia| clear - NUM; lia| exact F]. }
    assert (SUBt : forall X x, entries_nowrap X -> in_rangesb x (subF X) = true -> in_rangesb x X = true).
    { intros X x HX T. subst subF. destruct (mfa <? mfa'); [| exact T].
      apply (in_rangesb_subtract_true x X (FA s c + mfa) (FA s c + mfa')); [exact HX| clear - NUM; lia| clear - NUM; lia| exact T]. }
    assert (SUBfa : forall X x, entries_nowrap X -> mfa < mfa' -> FA s c + mfa <= bv_unsigned x < FA s c + mfa' -> in_rangesb x (subF X) = false).
    { intros X x HX LT R. subst subF. rewrite (proj2 (Z.ltb_lt _ _) LT).
      apply in_rangesb_subtract_inside; [exact HX| clear - NUM; lia| clear - NUM; lia| exact R]. }
    assert (SMONO : forall x, in_rangesb x (a_S s) = true -> in_rangesb x S' = true).
    { intros x T. rewrite ES, !in_rangesb_app, T, !Bool.orb_true_r. reflexivity. }
    assert (Es2 : a_sb s2 = a_sb s /\ a_pa s2 = a_pa s /\ (forall c0, RB s2 c0 = RB s c0)).
    { unfold a_sb, a_pa, RB, region_beg. cbn [a_st]. rewrite Fsb, Fpa. repeat split; reflexivity. }
    destruct Es2 as (Esb & Epa & ERB2).
    split; [split; [| split]|].
    - (* [comment removed for export] *)
      unfold amaps_in_ledger. change (a_st s2) with st'. change (a_L s2) with L'. fold h'. rewrite VMM, ENs, ELs, Fsec, Fmaps.
      assert (MAPS2 : forall mp, In mp ((if mfa <? mfa' then [mkMap (FA s c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false] else []) ++ as_maps st) ->
                In mp (as_maps st) \/ (mfa < mfa' /\ mp = mkMap (FA s c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false)).
      { intros mp Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [| left; exact Hin].
        destruct (Z.ltb_spec mfa mfa'); [| destruct Hin]. destruct Hin as [<-|[]]. right. split; [assumption| reflexivity]. }
      split.
      { intros mp Hin K1' K2' K3' K4'. destruct (MAPS2 mp Hin) as [Hin'|[_ ->]].
        - exact (IL1 mp Hin' K1' K2' K3' K4').
        - exfalso. exact (proj2 (K2' c) eq_refl). }
      split.
      { intros mp Hin KD x Hx. destruct (MAPS2 mp Hin) as [Hin'|[LT ->]].
        - destruct (IL2 mp Hin' KD x Hx) as [F1 F2]. split; [apply SUBf; [exact NWA| exact F1]| apply SUBf; [exact LNW| exact F2]].
        - cbn [mp_base mp_size] in Hx. split; [apply SUBfa; [exact NWA| exact LT| clear - Hx; lia]| apply SUBfa; [exact LNW| exact LT| clear - Hx; lia]]. }
      split.
      { intros sc x Hsc Hx. apply SUBf; [exact LNW| exact (IL3 sc x Hsc Hx)]. }
      split; [exact NOV|]. split; [exact NW|]. apply NWF. exact NWA.
    - (* [comment removed for export] *)
      unfold ashadow_visible. change (a_st s2) with st'. change (a_S s2) with S'. rewrite Fsec. destruct ASV as [V1 V2]. split.
      + intros c0 x Hc0 Hx. rewrite (ERB2 c0) in Hx. apply SMONO. apply (V1 c0 x Hc0).
        destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite Frg_c in Hx; cbn [rg_mapped_user] in Hx; exact Hx| rewrite (Frg_o c0 (proj1 Hc0) NE) in Hx; exact Hx].
      + intros sc x Hsc Hx. apply SMONO. exact (V2 sc x Hsc Hx).
    - (* [comment removed for export] *)
      unfold ABUDGET in ABU |- *. change (a_AL s2) with AL2. change (a_S s2) with S'.
      assert (PHI : aPhi s2 = aPhi s - ((mfa' - mfa) + 40960 * ((mfa' - mfa) / 262144))).
      { unfold aPhi. change (a_st s2) with st'. change (a_st s) with st.
        rewrite (pusage_grow st st' c ltac:(clear - HC; lia)).
        - rewrite Frg_c. cbn [rg_mapped_user rg_mapped_free_array]. fold r. fold mu mfa. rewrite Z.sub_diag. change (0 / 262144) with 0. clear; lia.
        - intros c' Hc' NE. rewrite (Frg_o c') by (clear - Hc' NE; lia). split; reflexivity.
        - fold r. fold mu. exact M6.
        - fold r. fold mfa. exact M3.
        - rewrite Frg_c. cbn [rg_mapped_user]. fold r. fold mu. rewrite Z.sub_diag. reflexivity.
        - rewrite Frg_c. cbn [rg_mapped_free_array]. fold r. fold mfa. exact M4.
        - rewrite Frg_c. cbn [rg_mapped_user]. fold r. fold mu. clear; lia.
        - rewrite Frg_c. cbn [rg_mapped_free_array]. fold r. fold mfa. clear - B6; lia. }
      rewrite PHI. fold h'. rewrite VML.
      destruct ABU as [AB0 AB1]. destruct HAL as [H0 H1].
      assert (KF : (mfa <? mfa') = true -> (mfa' - mfa) / 262144 = 1).
      { intros LT. apply Z.ltb_lt in LT. clear - LT M4 NUM. Z.div_mod_to_equations. lia. }
      assert (K0 : 0 <= (mfa' - mfa) / 262144) by (clear - NUM; apply Z.div_pos; lia).
      assert (PT : pages_total S' <= pages_total (a_S s) + 10 * ((mfa' - mfa) / 262144)).
      { rewrite ES, pages_total_app.
        assert (W1 : pages_total (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else []) <= 10 * ((mfa' - mfa) / 262144)).
        { destruct (mfa <? mfa'); [rewrite (KF eq_refl)| cbn; clear - K0; lia]. rewrite pages_total_cons. cbn [pages_total].
          pose proof (cl_bounds (wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))) as CB. cbn [fst snd] in CB. unfold wz in CB.
          rewrite (unsigned_lit ((mfa' - mfa) / 8)) in CB by (clear - NUM; Z.div_mod_to_equations; lia). unfold page_size in CB.
          assert (DV : (mfa' - mfa) / 8 / 4096 <= 8) by (clear - NUM; Z.div_mod_to_equations; lia). unfold wz. clear - CB DV. lia. }
        clear - W1. lia. }
      unfold page_size in *. clear - AB1 H0 H1 PT EAG NUM K0. unfold h. lia.
    - (* [comment removed for export] *)
      (* LPS 727298f3: [akernel] is [akernel_pre /\ akernel_resx]; this step changes neither the
         ledger nor the mappings ([VMR], [VMM]), so the reserved half carries over unchanged. *)
      unfold akernel. split; [| unfold akernel_resx in AKR |- *; cbv zeta in AKR |- *; change (m_vmmaps mo') with h'; rewrite VMR, VMM; exact AKR].
      unfold hsec in K10 |- *. fold h'. rewrite VMR, VML, VMT, VMM, ENs. change (a_thr s2) with (a_thr s). change (a_ctx s2) with (a_ctx s). rewrite Esb, Epa.
      change (a_fsb s2) with (a_fsb s). change (a_Zr s2) with (a_Zr s). change (a_L s2) with L'. change (a_st s2) with st'. rewrite Fsec. rewrite ELs.
      split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
      split; [intros a n c0 Hc0 Ha Hn; rewrite (ERB2 c0) in Ha, Hn; exact (K4a a n c0 Hc0 Ha Hn)|].
      split; [exact K4b|]. split; [exact K4c|]. split; [exact K5a|]. split; [exact K5b|].
      split.
      { intros x Hx. destruct (K5c x Hx) as [Z1 Z2]. split; [exact Z1|].
        pose proof sh_ceiling_lt_AHI_LO as SC. unfold AHI_LO in *. subst subF. destruct (mfa <? mfa'); [| exact Z2].
        apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; lia| clear - NUM; lia| exact Z2| clear - Hx SC NUM; lia]. }
      split; [intros x Hx; apply K6a; apply (SUBt _ x NWA Hx)|].
      split; [intros sc x Hsc Hx; apply (SUBf _ x NWA); exact (K6b sc x Hsc Hx)|].
      split; [exact K7|]. split; [exact K8a|]. split; [exact K8b|].
      split; [| split; [exact K9| split; [exact K10|]]].
      2:{ (* [comment removed for export] *)
          intros xa xn HB. subst subF. cbv beta. destruct (mfa <? mfa'); [apply LazyMadvise.region_free_maps_subtract; [exact NWA|]|]; exact (K11 xa xn HB). }
      { intros x Hx. destruct (K8c x Hx) as [Z1 Z2]. split; [exact Z1|].
        unfold sh, AIMG_TOP, ALOWSH_LO, ASHADOW_BASE in Hx. subst subF. destruct (mfa <? mfa'); [| exact Z2].
        apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; lia| clear - NUM; lia| exact Z2| clear - Hx NUM; lia]. }
  Qed.
End CDModel.

End HCW.
