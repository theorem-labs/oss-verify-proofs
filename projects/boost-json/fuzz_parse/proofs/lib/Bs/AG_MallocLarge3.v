(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require LazyMadvise.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepX AsDepotInv
     SecLazy SecLazy2 AS_AllocSec1 AG_LargeModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_MallocLarge3 () := KReplay.lz_vm "#$zwC89OSSVerify6Proofs:boost_json:fuzz_parse3lib2Bs8AsShadow4aappC13~~~C56Stdlib6ZArith6BinInt1Z3add!t/\5aceil!t0B2leK47Corelib7Numbers7BinNums8positive02!sK=1Z02!t,<6moduloI!sd+4Init5Logic3and00C!sA75proj1!tgG1C7!v=N8HeapCeil5h!v:Ht!wC\2sh!t+&!sh[;!x,$_facts!sqY9AllocRepX@sh_!st#ing_range!sw%K!w]<!vuQ>Asan!t;$Model8round_up!t4>2eq01I!s@;0!tM_9rq_needed!vU&4!xN&9micromega9SatDivModCZ_mod_nonneg!s,&!y#<7div!sU#!zr83not!~#=div!sC=mul!sC<=!tm#pos_b!vs#!sMA!u9#!sM15!ue$8PreO!s/#1Z;!u9#0_r_ext!sL>!st#!sL'!z4O3Lib9LiaTuning9zify_done!|xB7compare!yA29Datatypes3nat02K!x85=RingM!s4'5Psatz!sOM6!sO6:Z!sL+;!tu%!uk$!#5Y-!tk24list01!sFB2I!sFA0!tZ66VarMap1!ur9!sD,3I!sD?0I!v,C7Formula!tS87Env!sT#5PExpr!u^#!sIC!vI=6option!uE8!sk23!sI65Tauto8G!t}'6C!sJ<B!sJ&C!xP@=Z!sT$CheckerC!vd<4find!sqAC!sq0_s!}>#!#578or!w-8!wY:1!u~F4!sJF!vnG5!sJF8I!#>I>0!#>g?1!umD3Op203!xE<5eKi!vu4!|X-uni!|X9!se%4kind!}`?!sf$!#?_G3!#:A_kPageSiz!#<w>4True!#;k3!t{,:!#63$ison!~A8!#4w:0!#6d@1!#5jM!tk=4bool!t9>!sF%1!#5+?1!#ArT!#A#%8aapp_env!#9n%!wq^@kPtrArrayReserv!#:iB3sub!sC<4la!#=Z=3pow!sa=ones!v/\4a_AL!u0%c!sjR?AG_Ma!sn#Large37lg_cost!vye=as_n_r!vu%d!sve6as_sec!soe4zlen!#I5Z!w8,pa!yBB8max_spec!#DI=ax!sC<>pow!#DI#!#F5A:!sN#!sJB9!zX#_!yz$!#4:68eq_ind_r!#D<S2Nd:!t%#elimF3!vsY=AG_!z;$!#6;$l!s1#_geo!st%I!yI_schunk00!sq&!#7-<!#APE4!yC\?!#4^#sh_env_div!#L#Hdiv!#L#0!#<j?3!u7>3P!#739!#G\74!sOK7!sOK5!#9jM3!zAa7!#<`&!t?4!#@w27!x`E5!#@^H!sMJ!#Rn85False00!#;Salit!#5$a6AMODEL!slY!#W2+7akernel!snd!t]%X!snc9depot_cov!v>b?amaps_in_ledger!suds!#[N#_visible!sub7ABUDGET!#:ud!#>9f7as_!vL#!spfmp_kin!#>}%K!sp^5m!#J<#3!spl4!#3q&!#7<;N02I45stdpp9bitvector;definitions2bv00!#H3<prod!#^k`!v]#bas!yt'4ELinuxProcessSemantics?!s<25State8m_vm!x4$!s]P7vm!xj$!#a49x00C!v2@;bv_unsigned!uqcs!#NA'!u:Q;vm_noac!s;#!tRP<LazyRestrict:in!#ee$sb!}Mb3a_L!|Ze:sc!w`#_beg!sse;!ss&!w%-!stO:!vG#L!#6G#9nooverlap!sna>entries_nowra!#q2Ceqb!wVS<AS_!ux$Sec18as_m!v$#!xJY7Sec!u2#:nonvm_sam!#8QV3Lib4TacX2wz!#4=2!#3T71!{oU!#O$'!#3DPvm_limit!s]Q<vm_m!zc$ase!saQ6vm_brk!t>Ustart!saU=!#>N#subtract!#3,]eager_us!#o8+!#6856!#Na$!t5P9!t5#NodesAregion_free_app_!#@M&!#71?7Z_to_bv!#GPD7!ztT6M!wF%!#89&!#F@,!uYYB!uY/not_in!vm>9!#HE#!vpT!#3u,5zcovb!#4a`@!#8p+_!suf4zinb!uk8!~e-negb!sD=andb!tM[C!u9$_!{}1!t\&!yW&4Bool!s'$=!t8#_true_iff!#IV\6ak_l!#||'!t66!uf#!t6,!uQZ:!vx#_f!yJ#!t8%!#_Mb4lg_!#N&c!ur%!#9wY8!#9w%2I!w}6!ua/!vR[D!sx1!#=+/!#6'\z!|A'!{OC3orb!x~6:or!x}&r!tT]?!}n-con!#LVe<as_ptr_array!uPCapp!#L-^!#^T&1!|C25Lists4!s+#2In!s=7:in!#94#iff!$'}8or!#q53!s@,!$2f<8eqb!#dX#!#Lz;7reflect00!sk<6!sk#eq!#<+;sym!x~6>!#46#f!#8\$ff!sH7!#3H#!sH,!#FeZ!#3I#!z8#!}fY!#D_&C!#GU'!z9$!#;6#!yGCfst!sC=s!#;J\<entry!~91!uMZD!#I40!uR$'!|fe;compute_req!toY!#hl0:!#hl$!#X',!#O:Z2RB!uUe:get_!#A/$!sse>rg!uO#ped_us!#]wc3a_S!#3g1!|b,<!#7+'!#>;U!yI'5zin_W!#9Hb;pages_total!uib4aPhi!t^dwin_n!tc$Z!src9cl!$8@$s!spc5cl_lo!slg!v@eB!wx-!#uO&!sy%!$97;di!#q/$!tB\@!tB/!#>1h:as!}q&!#3Qb<!z6#!sr2!#R%O9!#Ep#_top!tR\5a_th!#3:b5a_ctx!}<d_!#_Wc5a_f!skd4a_Z!v0Z!#IZ+4hcnt!ske!$%o+!sk^!$%m+!#\3P!#TH,!#8:Z?!#^e+_a!zf#!tV&!#Cr58eq_trans!t:[Am!#?f$tains!~K/!vY\5ehigh!slc6sc!sm-!#c_;lt!#U6<6length!sc34Znat5Nat2Z9i!$,GC6of_na!$IpT!#}?/5!v+c8!vr$_!#c~&!so]Dzsum!#i>#_filter_!$Yp+!s{\?zlen!svn9!}3#!zJh9hcnt!#:aZ;!|-#MadviseI!#_W-!#[;6!y6V;!y6+18!u_Y:AsDepotInv4d_nb!slg!#8XW!{X48!skg9!skg6!sk%!#VB^7mapping!#VC+!#k<O!#6`-!#4[+!#Vh$7!s+#Def3ma!#?uS6SecGap4!~1#!tg'!#Wm46!}N%I!uvg!$8i&!sr^!$#6%0!w\e!sp&2!spl6!spl!{d&!$IhA2!#Gw^7PROT_RW!u&l7!{BW9page!#{]$!s^PBtarget_!#HY$!#v9$!#83[4AHC0!#5QX!sk0L!skd7ASECMAX!t[fSB!skY!$jR'6AHI_LO!uIeHSB_!#\>&I!#zCPVmMaps!$=FT5ASegs8AIMG_TOP!v$b9ALOWSH!v',!|;^AkChunksBlockCount!#6x<8ni!#SE%!t?^;kNumClasses!#6|d6!#@U$!#6}&!#U$_kSpac!$ZW,!wfU!yz&8AFS_SIZE!tce;kR!uW$!td]!z9%7!z9$!yG'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk44listk44prod46Stdlib6ZArith6BinInt1Zma3addk44boolma3mul3h5LinuxProcessSemanticsfLinuxProcessSem5Statep5dmaps_subtractma3eqbma3div79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX~~~~~~tf7AMODELXtf9depot_covma2lt37Corelib4Init5Logichj93andma3powp58m_vmmapsp57vm_maps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~hmf3a_L69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~hr44rsub69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~hv5eentries_nowrap" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition lg_L : ltac2:(zQ "52!h9!jc!k1!lc!m3&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>1L~1>2pa$2>4nres$2>3nch$2~1") := ltac2:(zQ "a2!h9!jc!k1!o2!o8!lc!m3!of!s3!t3&@2$6@1$1@1$0#k0@1$1@1$0#k0&@1$5~0\1L~1\2pa$2\4nres$2\3nch$2M4\0$4~1@2$9^1^2@3$8^4@2$3^3@2$7+8^2@2$3@2$3^3@2$7+8^2+iggg0^4").
(* [comment removed for export] *)
Definition lg_cost : ltac2:(zQ "10!k1>3msz$0$0") := ltac2:(zQ "40!o2!k1!t9!of\3msz$1@2$0@2$0^1+iggg0@2$3@2$0@2$2^1+ogg0+2+hgg0").

Section ModelAfterLarge.
  Variables (s : ast) (mo mo2 : Model) (a size : Z) (d : depot).
  Let st := a_st s.
  Let pa := a_pa s.
  Let r := compute_req size.
  Let needed := rq_needed r.
  Let msz := round_up needed kPageSize + kPageSize.
  Let nch := zlen (as_sec st).
  Let nres := as_n_reserved st.
  Let st2 := large_state st a size.
  Let Wsh : word * word := (wz (sh a), wz (msz / 8)).
  Let L2 := lg_L (a_L s) pa nres nch.
  Let AL2 := a_AL s - lg_cost msz.
  Let s2 := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 (Wsh :: a_S s) (a_Zr s) AL2 (a_top s) (a_bot s).

  Hypothesis AMX : ltac2:(zQ "10!hhe@3$0?5HCEIL?1s?2mo").
  Hypothesis DCOV : ltac2:(zQ "10!hi8@2$0?1d?2mo").
  Hypothesis SZ : ltac2:(zQ "30!hj4!hkd!hl4@2$1@2$0+vsg0?4size@2$0?4size@2$2+2+i0").
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0.
  Hypothesis FREE : region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true.
  Hypothesis LM : ltac2:(zQ "40!hla!hm5!hqd!hud@2$3@1$2?1s@1$1@1$0?2mo").         (* [comment removed for export] *)
  Hypothesis NWL : ltac2:(zQ "20!hqd!ij2@1$1@1$0?1s").                        (* [comment removed for export] *)
  Hypothesis ALLOW : lg_cost msz <= a_AL s.
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil.
  Hypothesis NCH : 0 <= nch <= nres /\ nres + 16384 <= 2^20.
  Hypothesis MO : as_model mo a msz pa nres (nch =? nres) mo2.

  Let ARE : 7417856 <= a /\ a + msz <= aceil. Proof. pose proof (proj1 AR) as X. clear - X. aunf. lia. Qed.   (* [comment removed for export] *)
  Let PAE : 7417856 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let RQ := large_req size SZ.

  Let GEO : size + 8 <= needed - 4088 /\ needed <= size + 4104 /\ needed + 4096 <= msz /\ msz < needed + 8192 /\ needed mod 8 = 0 /\ msz mod 4096 = 0 /\ a mod 4096 = 0.
  Proof.
    apply (large_geo st a size SZ). ndestruct AR as (_ & _ & AL). unfold kPageSize. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. exact AL.
  Qed.
  (* [comment removed for export] *)
  Let BND : 7417856 <= a /\ a + msz <= aceil /\ 73728 <= msz /\ 7417856 <= pa /\ pa + 8388608 <= aceil
            /\ 2148314624 <= sh a /\ sh a + msz / 8 <= (sh aceil) /\ 8 * (msz / 8) = msz.
  Proof.
    ndestruct AR as (A1 & A2 & A3). npose GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7). destruct PAR as [P1 P2].
    pose proof (aapp_sh_env_div _ _ A1 ltac:(clear - G1 G3 SZ; lia)) as ASH.
    apply aapp_env in A1; [| clear - G1 G3 SZ; lia]. apply aapp_env in P1; [| unfold kPtrArrayReserve; clear; lia].
    acb. unfold AHI_LO, kPtrArrayReserve in *. subst pa.
    unfold round_up, round_down, sh, ASHADOW_BASE in *. repeat split; try lia; Z.div_mod_to_equations; lia.
  Qed.
  (* [comment removed for export] *)
  Let PBAND : pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa.
  Proof. pose proof (aapp_lit _ _ (proj1 PAR)) as L. unfold kPtrArrayReserve in L. exact L. Qed.

  Theorem amodelx_after : AMODELX s2 mo2 /\ depot_cov d mo2.
  Proof.
    (* LPS revision repair (75d69e00, checker 2c6b6db8).  This proof was a KReplay replay that
       destructured amaps_in_ledger's SIX conjuncts at their PRE-RESTATEMENT shape (As:85 /
       Bs:86), and that definition's first conjunct is now guarded by a non-zero ledger-word
       size (As//Bs AllocRep.v, same series).  Written out as plain text; the STATEMENT IS
       UNCHANGED.  Text from a donor tree:projects/openssl/echconfiglist_parser/
       proofs/lib/As/AG_MallocLarge3.v:79-214, the same theorem in the same Section, already
       plain text there.  It carries no address of its own: every bound is AHI_LO / AIMG_TOP /
       ALOWSH_LO / aceil, so nothing is transposed between trees.
       EXACTLY TWO STEPS DIFFER from the donor, both in the first conjunct, because the goal is
       now the WEAKER guarded one: the new section map's membership is produced under `intros
       _`, and a carried entry's membership is re-wrapped as `fun POS => or_intror (X POS)`. *)
    destruct AMX as [AM AK]. destruct AM as (AIL & ASV & AB). destruct AIL as (A1 & A2 & A3 & NOV & NW & NWA).
    pose proof MO as M; unfold as_model in M; cbv beta iota zeta in M. destruct M as (NV & VM2 & VR2 & VL2 & VB2 & VK2 & VS2 & VA2 & EAG2).
    pose proof BND as B. destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). acb. pose proof PBAND as PB'.
    assert (SHLO : sh AHI_LO = 0x2008fff7000) by (rewrite <- AHSB_eq; reflexivity). pose proof sh_ceiling_range as SCV.
    set (h := m_vmmaps mo) in *. set (h2 := m_vmmaps mo2) in *.
    assert (NOTL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (a_L s) = false).
    { intros x Hx. destruct (in_rangesb x (a_L s)) eqn:E; [exfalso| reflexivity].
      pose proof (LM x E) as INM. rewrite (region_free_not_in _ _ _ x (region_free_app_r _ _ _ _ FREE)) in INM; [discriminate|].
      unfold wz. rewrite !unsigned_lit by lia. exact Hx. }
    assert (SUBL : forall x : word, in_rangesb x L2 = true -> in_rangesb x (a_L s) = true).
    { intros x Hx. subst L2. unfold lg_L in Hx. destruct (nch =? nres); [| exact Hx]. rewrite in_rangesb_zcovb in Hx |- *.
      rewrite zcovb_maps_subtract in Hx by (first [exact NWL| lia]). apply andb_true_iff in Hx. exact (proj1 Hx). }
    assert (BANDL : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L2 = true).
    { intros x Hx. pose proof (ak_lsh s mo AK x Hx) as LX. rewrite SHLO in Hx. subst L2. unfold lg_L.
      destruct (nch =? nres); [| exact LX]. rewrite in_rangesb_zcovb in LX |- *. rewrite zcovb_maps_subtract by (first [exact NWL| lia]).
      rewrite LX. apply andb_true_iff. split; [reflexivity|]. apply negb_true_iff. apply zinb_false. lia. }
    assert (BANDL2 : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x L2 = true).
    { intros x Hx. pose proof (ak_lsl s mo AK x Hx) as LX. unfold sh, AIMG_TOP, ALOWSH_LO, ASHADOW_BASE in Hx. subst L2. unfold lg_L.
      destruct (nch =? nres); [| exact LX]. rewrite in_rangesb_zcovb in LX |- *. rewrite zcovb_maps_subtract by (first [exact NWL| lia]).
      rewrite LX. apply andb_true_iff. split; [reflexivity|]. apply negb_true_iff. apply zinb_false. lia. }
    assert (NASUB : forall x : word, in_rangesb x (vm_noaccess h) = false -> in_rangesb x (vm_noaccess h2) = false).
    { intros x Hx. rewrite VA2. rewrite in_rangesb_zcovb in Hx |- *.
      destruct (nch =? nres); [apply zcovb_maps_subtract_false; [exact NWA| lia| lia| exact Hx] | exact Hx]. }
    assert (NWA2 : entries_nowrap (vm_noaccess h2)).
    { rewrite VA2. destruct (nch =? nres); [apply maps_subtract_nowrap; [exact NWA| lia| lia] | exact NWA]. }
    assert (INCONS : forall (x : word) e, in_rangesb x (vm_maps h) = true -> in_rangesb x (e :: vm_maps h) = true)
      by (intros x e Hx; rewrite in_rangesb_cons, Hx; apply orb_true_r).
    split; [| intros x Hx; unfold h2 in VM2 |- *; rewrite VM2; apply INCONS; exact (DCOV x Hx)].
    split.
    { split.
      { unfold amaps_in_ledger. change (m_vmmaps mo2) with h2. change (a_st s2) with st2. change (a_L s2) with L2.
        change (as_maps st2) with (large_maps st a size). change (as_sec st2) with (as_sec st ++ [mkSC a msz needed]).
        unfold large_maps. fold r needed msz nch nres. fold nch. fold nres.
        split.
        { intros mp Hin K1 K2 K3 K4. rewrite VM2. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
          - exfalso. destruct (nch =? nres); [| destruct Hin]. destruct Hin as [<-|[]]. exact (K3 eq_refl).
          - destruct Hin as [<-|Hin]; [split; [intros _; left; reflexivity| cbn [mp_base]; clear - B1 B2 B3; acb; lia]|].
            destruct (A1 mp Hin K1 K2 K3 K4) as [X Y]. exact (conj (fun POS => or_intror (X POS)) Y). }
        split.
        { intros mp Hin KK x Hx. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
          - destruct (Z.eqb_spec nch nres) as [EC|NE]; [| destruct Hin]. destruct Hin as [<-|[]]. cbn [mp_base mp_size] in Hx.
            assert (SL : pa + 8 * nres <= bv_unsigned x < pa + 8 * nres + 131072) by (change (as_ptr_array st) with pa in Hx; unfold kChunksBlockCount in Hx; fold nres in Hx; lia).
            split.
            + rewrite VA2. rewrite in_rangesb_zcovb. replace (nch =? nres) with true by (symmetry; apply Z.eqb_eq; exact EC).
              assert (N1 : zcovb (maps_subtract (vm_noaccess h) (pa + 8 * nres) (pa + 8 * nres + 131072)) (bv_unsigned x) = false).
              { rewrite zcovb_maps_subtract by (first [exact NWA| lia]). apply andb_false_iff. right. apply negb_false_iff. apply zinb_true. exact SL. }
              exact N1.
            + subst L2. unfold lg_L. replace (nch =? nres) with true by (symmetry; apply Z.eqb_eq; exact EC). rewrite in_rangesb_zcovb.
              assert (N1 : zcovb (maps_subtract (a_L s) (pa + 8 * nres) (pa + 8 * nres + 131072)) (bv_unsigned x) = false).
              { rewrite zcovb_maps_subtract by (first [exact NWL| lia]). apply andb_false_iff. right. apply negb_false_iff. apply zinb_true. exact SL. }
              exact N1.
          - destruct Hin as [<-|Hin]; [exfalso; destruct KK as [K|[[c [K|K]]|K]]; discriminate K|].
            destruct (A2 mp Hin KK x Hx) as [Q1 Q2]. split; [exact (NASUB x Q1)|].
            destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q2. discriminate Q2. }
        split.
        { intros sc x Hin Hx. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]].
          - pose proof (A3 sc x Hin Hx) as Q. destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q. discriminate Q.
          - cbn [sc_map_beg sc_map_size] in Hx. pose proof (NOTL x Hx) as Q. destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q. discriminate Q. }
        rewrite VM2. split; [| split; [| exact NWA2]].
        - apply nooverlap_cons_free; [exact (region_free_app_r _ _ _ _ FREE)| exact NOV].
        - apply entries_nowrap_cons'; [| exact NW]. unfold entry_nowrap, LazyLedger.hi, LazyLedger.lo. cbn [fst snd]. unfold wz. rewrite !unsigned_lit by lia. lia. }
      split.
      { destruct ASV as [V1 V2]. unfold ashadow_visible. change (a_st s2) with st2. change (a_S s2) with (Wsh :: a_S s).
        change (as_sec st2) with (as_sec st ++ [mkSC a msz needed]).
        split.
        - intros c x Hc Hx. rewrite in_rangesb_cons. rewrite (V1 c x Hc); [apply orb_true_r|].
          change (RB s2 c) with (RB s c) in Hx. change (get_region st2 c) with (get_region st c) in Hx. exact Hx.
        - intros sc x Hin Hx. rewrite in_rangesb_cons. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]].
          + rewrite (V2 sc x Hin Hx). apply orb_true_r.
          + cbn [sc_map_beg sc_map_size] in Hx. apply orb_true_iff. left. subst Wsh. apply (zin_W (sh a) (msz / 8)); lia. }
      destruct AB as [AB0 AB1]. unfold ABUDGET. change (a_AL s2) with AL2. change (a_S s2) with (Wsh :: a_S s). change (m_vmmaps mo2) with h2. rewrite VL2.
      rewrite (aPhi_regions s s2) by reflexivity.
      rewrite pages_total_cons. pose proof (cl_bounds Wsh) as CB. subst Wsh. cbn [fst snd] in CB. unfold wz in CB. rewrite (unsigned_lit (msz / 8)) in CB by (first [clear - SZ ARE GEO BND B8 ACEILB CB; lia | lia]).
      pose proof (pages_total_nonneg (a_S s)) as PT. unfold page_size in *.
      replace (msz / 8 / 4096) with (msz / 32768) in CB by (rewrite Z.div_div by lia; reflexivity).
      subst AL2. unfold lg_cost in *. split; [lia|]. clear - AB1 CB PT EAG2 ALLOW B3; try acb. unfold wz in *. subst h. destruct (nch =? nres); lia. }
    destruct AK as ((K1 & (K2a & K2c) & K3 & K4a & K4b & K4c & K5a & K5b & K5c & K6a & K6b & K7 & K8a & K8b & K8c & K9 & K10 & K11) & AKR).
    unfold akernel. split.
    2:{ (* LPS 727298f3: [akernel_resx].  The ledger is unchanged ([VR2]), so the same intervals
           witness it; a large allocation conses its window onto the mappings ([VM2]), and that
           window misses the whole ledger by [FREE], the check the mmap commit made. *)
        unfold akernel_resx in AKR |- *. cbv zeta in AKR |- *. change (m_vmmaps mo2) with h2.
        destruct AKR as [rx [Hrx [Hok [Hcnt [Hsz HD]]]]]. exists rx. rewrite VR2, VM2.
        split; [exact Hrx|]. split; [exact Hok|]. split; [exact Hcnt|]. split; [exact Hsz|].
        intros iv Hiv [eb es] He. destruct Hiv as [<-|Hiv]; [| exact (HD iv Hiv (eb, es) He)].
        pose proof (State.region_free_In _ _ _ eb es FREE (in_or_app _ _ _ (or_introl He))) as OV.
        unfold iv_overlap in OV. cbn [fst snd]. apply andb_false_iff in OV.
        destruct OV as [OV|OV]; apply Z.ltb_ge in OV; [right|left]; lia. }
    change (m_vmmaps mo2) with h2. change (a_thr s2) with (a_thr s). change (a_ctx s2) with (a_ctx s). change (a_sb s2) with (a_sb s).
    change (a_pa s2) with pa. change (a_fsb s2) with (a_fsb s). change (a_Zr s2) with (a_Zr s). change (a_L s2) with L2.
    rewrite VR2, VL2, VM2.
    split; [exact K1|]. split; [exact (conj K2a (eq_trans (nonvm_same_atop _ _ NV) K2c))|].
    split; [intros x Hx; apply INCONS; exact (K3 x Hx)|].
    split; [intros xa xn c Hc H1 H2; apply map_contains_cons; change (RB s2 c) with (RB s c) in H1, H2; exact (K4a xa xn c Hc H1 H2)|].
    split; [intros xa xn H1 H2; apply map_contains_cons; exact (K4b xa xn H1 H2)|].
    split; [intros xa xn H1 H2 H3; apply map_contains_cons; exact (K4c xa xn H1 H2 H3)|].
    split; [exact K5a|]. split; [exact K5b|].
    split; [intros x Hx; split; [exact (proj1 (K5c x Hx))| exact (BANDL x Hx)]|].
    split.
    { intros x Hx. apply INCONS. apply K6a. destruct (in_rangesb x (vm_noaccess h)) eqn:E. { unfold h in E. first [exact E| reflexivity]. } rewrite (NASUB x E) in Hx. discriminate Hx. }
    split.
    { intros sc x Hin Hx. change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]) in Hin. apply in_app_iff in Hin.
      assert (E0 : in_rangesb x (vm_noaccess h) = false).
      { destruct Hin as [Hin|[<-|[]]]; [exact (K6b sc x Hin Hx)|]. cbn [sc_map_beg sc_map_size] in Hx.
        destruct (in_rangesb x (vm_noaccess h)) eqn:E; [exfalso| reflexivity].
        pose proof (K6a x E) as INM. rewrite (region_free_not_in _ _ _ x (region_free_app_r _ _ _ _ FREE)) in INM; [discriminate|].
        unfold wz. rewrite !unsigned_lit by lia. exact Hx. }
      destruct (in_rangesb x (vm_noaccess h2)) eqn:E2; [| reflexivity]. rewrite (NASUB x E0) in E2. discriminate E2. }
    split.
    { intros sc Hin. change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]) in Hin. apply in_app_iff in Hin.
      destruct Hin as [Hin|[<-|[]]]; [right; exact (K7 sc Hin)| left; reflexivity]. }
    split; [intros x Hx; apply INCONS; exact (K8a x Hx)|].
    split; [intros xa xn H1 H2 H3; apply map_contains_cons; exact (K8b xa xn H1 H2 H3)|].
    split; [intros x Hx; split; [exact (proj1 (K8c x Hx))| exact (BANDL2 x Hx)]|].
    split; [exact K9|].
    split.
    2:{ intros xa xn HB. pose proof (K11 xa xn HB) as FR0. rewrite VA2.
        destruct (nch =? nres); [apply LazyMadvise.region_free_maps_subtract; [exact NWA| exact FR0]| exact FR0]. }
    { destruct K10 as (C1 & C2 & C3). change (as_sec st2) with (as_sec st ++ [mkSC a msz needed]). unfold hsec in *.
      rewrite hcnt_cons, hlen_cons, zlen_filter_app, zsum_size_filter_app. rewrite (ehigh_wz a msz) by lia.
      assert (SH : forall z, schigh (mkSC a msz z) = (AHI_LO <? a + msz)) by (intros z; reflexivity). rewrite !SH.
      cbn [List.filter snd]. rewrite !SH. replace (bv_unsigned (wz msz)) with msz by (unfold wz; rewrite unsigned_lit by lia; reflexivity).
      split; [| split].
      - destruct (AHI_LO <? a + msz); unfold zlen in *; cbn [length map] in *; clear - C1; subst h st; change (Z.of_nat 1) with 1; change (Z.of_nat 0) with 0; lia.
      - destruct (AHI_LO <? a + msz); cbn [map SecGap.zsum sc_map_size] in *; clear - C2; subst h st; repeat match goal with x := _ |- _ => subst x end; lia.
      - intros sc Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]]; [exact (C3 sc Hin)|].
        cbn [sc_map_size]. unfold ASECMAX. pose proof GEO as (G1 & G2 & G3 & G4 & _). clear - G1 G2 G3 G4 SZ. subst msz needed r. lia. }
  Qed.
End ModelAfterLarge.

End HCW.

