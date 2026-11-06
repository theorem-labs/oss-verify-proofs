(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore AsanPlan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes06option37Corelib7Numbers7BinNumsi01N79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~jd4expr03nat04None04Some89OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsanPlanF2FC8WithSegs~~~~~~p64fvar46Stdlib6NArith6BinNat1Nu56of_nat04bool05false04trueu53eqb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~hhf4amap04listhhfcinside_mapsB04prod03sndp67splitby03fst37Corelib4Init5Logichp52eq37Corelib5Lists7ListDefhqf3mapi01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3libbAxSymExec3B4AX2B~~~~~~ht14bctx01S06lengthhhf3KHIhhf6covershhfblit_entrieshhfashadow_off46Stdlib6ZArith6BinInt1Zil53sub04pairhhf7am_basep64nkeyp64mksFhhfbsafe_rangeBp64covFp6bsafe_rangeFjd6kentryjd5saddrjd4ELit46Stdlib5Arith8PeanoNat3Natisf3lebil56of_nathhfdgrant_keep_bBp6dgrant_keep_bF36Stdlib5Lists4Listjhc6filterhhf9kimg_clipht14mkbchhfh0kn_grant_filterMp6h0kn_grant_filterFjhc2Inhp53andhp52exhhfakentry_eqbp65seekKp68ent_walk69OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec3~~~~~~jqb8existsbLjhc7forallbhhf3acshhf8list_eqbil53lebhhf4a_sshhf2knjd6sentryhhf8a_abyteshhf5a_brkhhf7a_eagerhhf4a_fdhhf7a_ghosthhf6a_mapshhf8a_tidsethhf7a_totszhhf5a_vishhf7a_vmopshhf5a_ylohhf8pair_eqbhhf2pcjd8expr_eqbjd6s_regshhf7afd_eqbhhf8amap_eqbhhf4vmophhf8vmop_eqbjd5s_log36Stdlib4Bool4Boolkva3eqbil53eqbhhf7entailsp68entailsFhhf5mkind03app04andb04conshhf3nxtjd4EVarjd2SA04negb03nil03orbhhf2AMhhf7CEILMAXhhf9add_entryhhf9budget_okhhf6escalehhfcexpr_vars_lthhf8fresh_okhhf6gap_okhhfbkdisj_fixedhhf9kdisj_newhhfckdisj_shadowhhf8mmap_lenhhf8no_holeshhf9null_kendhhf7vis_addjd6KRangejd3KWrjd5KZerojd6sr_updil53divil53mulhhf7KRWLAZYhhf9mkind_eqbhhf3reghhfcshadow_factshhfawith_maps0jhc8flat_maphhf6am_lenhhfafixed_argsp6h1mmap_fixed_grantFjderanges_apart_xhhf4CEILhhf9find_holehhf7is_holehhf6no_foghhf6unholei08positivep6h0mmap_fixed_freeFp6ammap_nullFhhf9KNONELAZYhhf5KNONEhhf3KRWhhf9mmap_gatehhf6refusehhf9gap_childhhf7gaps_ofhhf7opt_allhhf9mmap_nullhhfh0mmap_fixed_granthhffmmap_fixed_freehhfanode_mmap2p6bnode_mmap2Fhhfdnode_mmapgapsp6enode_mmapgapsF3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeog37Segmentjd4itabhhf6atablehhf6spiece" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FC.
Import AX2. Import AX2B. Import AP.

Section WithSegs.
Variable segs : ltac2:(zQ "20!hm5!oj8@1$0$1").
Variable IT : ltac2:(zQ "10!ok3$0").
Variable A : ltac2:(zQ "10!oka$0").
Variable nx0 : nat.
Variable LIMIT : Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint fvar (e : expr) : option nat :=
  match e with
  | EVar n => Some n
  | ELit _ => None
  | EBlob _ _ _ _ => None
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => match fvar a with Some n => Some n | None => fvar b end
  | EExt _ _ _ a => fvar a
  end.
Definition nkey : ltac2:(zQ "30!h8!j9!ne>1e$2@1$0$1") := ltac2:(zQ "80!h8!j9!o5!oa!p0!te!ne!vd\1e$6M0\1x@1$0$2@1$0$1@1$5^1\1v$2@2$4$1@1$7^1@1$3$1").
Definition okN_eqb : ltac2:(zQ "30!h8!j9!hg6>1a@1$0$1>1b@1$0$1$2") := ltac2:(zQ "60!h8!j9!hg6!hgc!hh3!hh9\1a@1$0$1\1b@1$0$1M0\1a@1$0$1$2^2\1x$1M0\1b@1$0$1$2^2\1y$1@2$5^2^1$3M0\1b@1$0$1$2^1\1n$1$3$4").

(* [comment removed for export] *)
Fixpoint splitby (kb : option N) (mks : list (option N * amap)) : list amap * list amap :=
  match mks with
  | [] => ([], [])
  | (k, m) :: rest => let '(l1, l2) := splitby kb rest in if okN_eqb kb k then (m :: l1, l2) else (l1, m :: l2)
  end.

Lemma inside_mapsB_split : ltac2:(zQ "h00!hld!hm5!hg6!h8!j9!hmb!hnb!ho1!ho6!ne!hp0!hh3!hq9!hs6!hsd!ih4>2bc$f>2kb@1$3$4>3mks@1$1@2$6@1$3$4$0>1b$9>3off$e>3len$9@3$c$2M2\0$2$2@5$5^6@3$a@1$1$0@1$1$0@2$8^5^4^3^2^1$b@5$5^6@3$7@1$1$0@1$1$0@2$8^5^4^3^2^1@5$5^6@4$d@2$6@1$3$4$0$0@2$7@1$3$4$0^4^3^2^1").
Proof.
  intros bc kb mks b off len. induction mks as [|[k m] rest IH]; [reflexivity|].
  cbn [splitby map snd]. destruct (splitby kb rest) as [l1 l2]. cbn [fst snd] in IH.
  cbn [inside_mapsB]. rewrite <- IH.
  destruct (okN_eqb kb k); cbn [fst snd inside_mapsB];
    destruct (negb (is_fog m)); try destruct (xinside_cB bc b off len (am_base m) 0 (am_len m));
    destruct (inside_mapsB bc l1 b off len); destruct (inside_mapsB bc l2 b off len); reflexivity.
Qed.

(* [comment removed for export] *)
Definition safe_rangeF (bc : bctx) (cov : bool) (mks : list (option N * amap)) (b : expr) (off : Z) (len : expr) : bool :=
  if match xhiB bc len, base_rangeB bc b with
     | Some lh, Some (lo, hi) =>
         if (if Z.leb (img_lo A) (lo + off) then Z.leb (hi + off + lh) (img_hi A) else false) then true
         else if (if Z.leb (shadow_off A - 4096) (lo + off) then if Z.ltb (hi + off) KHI then if Z.leb (hi + off + lh) KHI then cov else false else false else false) then true
         else (if stack_side_xB bc b off then if Z.leb 0 (lo + off) then Z.leb (hi + off + lh) two64 else false else false)
     | _, _ => false
     end then true
  else let '(l1, l2) := splitby (nkey b) mks in
       if inside_mapsB bc l1 b off len then true else inside_mapsB bc l2 b off len.

Definition covF : ltac2:(zQ "30!hg6!hm5!hld>2ms@1$1$2$0") := ltac2:(zQ "90!hld!ihc!ihf!hm5!ii7!iie!ij8!ik7!imd\2ms@1$3$0@4$5@1$1@2$2$0^1@1$6^1@2$8@1$7?1A+hgg0$4").
Definition mksF : ltac2:(zQ "50!hm5!hld!h8!hnb!j9>2ms@1$0$1@1$0@2$3@1$2$4$1") := ltac2:(zQ "90!hld!h8!j9!hm5!in4!hnb!hs6!ina!io5\2ms@1$3$0@4$6$0@2$5@1$1$2$0\1m$0@4$4@1$1$2$0@1$8@1$7^1^1^1").
Lemma mksF_snd : ltac2:(zQ "90!hld!hm5!h8!j9!hnb!ho1!hq9!hs6!ioc>2ms@1$1$0@3$6@1$1$0@4$7@2$4@1$2$3$0$0@2$5@1$2$3$0@1$8^1^1").
Proof. intros ms. unfold mksF. induction ms as [|m rest IH]; [reflexivity|]. cbn [map snd]. rewrite IH. reflexivity. Qed.

Lemma safe_rangeF_eq0 : ltac2:(zQ "f1!hld!h8!j9!hnb!ho1!hs6!ne!hg6!hm5!hq9!hsd!ip3!iq2!iq9!ih4&@4$5@2$3@1$1$2$0$0@2$4@1$1$2$0^4>2bc$e>3mks@1$8@2$3@1$1$2$0>1b$6>3off$a>3len$6@3$9$7@6$d^5@1$c~0^4^3^2^1@6$b?1A^5~0^3^2^1").
Proof.
  intros bc mks b off len. unfold safe_rangeF, safe_rangeB, covF.
  rewrite <- (inside_mapsB_split bc (nkey b) mks).
  destruct (splitby (nkey b) mks) as [l1 l2]. cbn [fst snd].
  destruct (xhiB bc len) as [lh|]; [|reflexivity]. destruct (base_rangeB bc b) as [[lo hi]|]; [|reflexivity].
  destruct (stack_side_xB bc b off), (Z.leb 0 (lo + off)), (Z.leb (hi + off + lh) two64), (Z.leb (img_lo A) (lo + off)),
    (Z.leb (hi + off + lh) (img_hi A)), (Z.leb (shadow_off A - 4096) (lo + off)), (Z.ltb (hi + off) KHI), (Z.leb (hi + off + lh) KHI),
    (covers (Datatypes.S (length (map snd mks))) (lit_entries (map snd mks)) (shadow_off A - 4096) KHI); reflexivity.
Qed.
Lemma safe_rangeF_eq : ltac2:(zQ "b0!ne!hg6!hm5!hq9!hsd!hld!ip3!iq2!ioc!iq9!ih4>2bc$a>2ms@1$2$5>1b$0>3off$4>3len$0@3$3$1@6$9^5@1$7^4@1$8^4^3^2^1@6$6?1A^5^4^3^2^1").
Proof. intros bc ms b off len. rewrite <- (mksF_snd ms) at 1 3. apply safe_rangeF_eq0. Qed.

Definition grant_keep_bF : ltac2:(zQ "80!hg6!hm5!h8!hnb!j9!hld!ir7!ih4>2bc$7>3cov$0>3mks@1$1@2$3@1$2$4$5>1K$6$0") := ltac2:(zQ "h26!is0!ne!hsd!hg6!iq9!hh3!ir7!o5!hgc!hm5!h8!hnb!j9!hld!is8!ih4!iua!iv1&\1b$1\1o$2@6$4^8^7^6^2^1^3&M0\1a$0$3^2~0&\1l$1~1&\1a$0~2&\1b$1\1o$2@6$4^9^8^7^2^1^4&M0\1a$0$3^3~4\2bc$f\3cov$3\3mks@1$9@2$b@1$a$c$d\1K$6M6\1K$6$3^1\1a$0\1w$7\1v$1M0\1a$0$3^3\1b$1\1o$2M3\0$3$3@2$h0^4N8@6$4^9^8^7^2^1@1$e@1$h1^4$8~3\1a$0\1l$1\1k$7~5\2lo$2\2hi$2$5\1e$1\1m$2$5\1e$1\2lo$2\2hi$2$5\1a$0\1n$1~1\2a1$0\2n1$1\2a2$0\2n2$1$5\1a$0\1l$1\1c$2~5~3").
Lemma grant_keep_bF_eq : ltac2:(zQ "a0!hg6!hm5!hq9!hld!ivb!iq2!jgc!ioc!ir7!ih4>2bc$9>2ms@1$1$3>1K$8@3$2$0@4$6^3@1$5^2@1$7^2^1@4$4?1A^3^2^1").
Proof.
  intros bc ms K. unfold grant_keep_bF, grant_keep_bB.
  destruct K as [[b o] w v|[b o] l|[b o] l bk|lo hi|e m|e lo hi|[b o] n|a1 n1 a2 n2|[b o] l c|[b o] l];
    rewrite ?safe_rangeF_eq; reflexivity.
Qed.

Lemma filter_exteq : ltac2:(zQ "40!hg6!hm5!hq9!jif>1TT>1f>0^1$0>1g>0^2$0>1l@1$1^3>0>1x^4@3$2$0@1^4^1@1^3^1@3$2@1$1^5@3$3^5^4^2@3$3^5^3^2").
Proof. intros T f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [List.filter]. rewrite H, IH. reflexivity. Qed.

(* [comment removed for export] *)
Definition kn_grant_filterF : ltac2:(zQ "30!hm5!ir7!hld>1k@1$0$1>2ms@1$0$2@1$0$1") := ltac2:(zQ "e0!hm5!hld!ir7!hg6!h8!hnb!j9!jj9!iq2!jgc!ioc!ih4!jk6!jif\1k@1$0$2\2ms@1$0$1=2bc$b@1$c^2=3cov$3@1$8^2=3mks@1$0@2$5@1$4$6$1@1$a^3@2$7?1A@3$d$2@3$9^3^2^1^5").
Lemma kn_grant_filterF_eq : ltac2:(zQ "60!hm5!ir7!hq9!hld!jke!jm3>1k@1$0$1>2ms@1$0$3@3$2@1$0$1@2$5^2^1@3$4?1A^2^1").
Proof.
  intros k ms. unfold kn_grant_filterF, kn_grant_filterM, kn_grant_filterB. cbv zeta.
  replace (bc_fk (mkbc k)) with k by reflexivity.
  rewrite (filter_exteq _ (grant_keep_bF (mkbc k) (covF ms) (mksF ms)) (grant_keep_bB A (mkbc k) ms) k (grant_keep_bF_eq (mkbc k) ms)).
  reflexivity.
Qed.
Lemma kn_grant_filterF_feq : ltac2:(zQ "60!hm5!ir7!hq9!hld!jke!jm3@3$2>1k@1$0$1>2ms@1$0$3@1$0$1$5@1$4?1A").
Proof. apply functional_extensionality; intros k. apply functional_extensionality; intros ms. apply kn_grant_filterF_eq. Qed.

(* [comment removed for export] *)
Fixpoint seekK (K : kentry) (c : list kentry) : option (list kentry) :=
  match c with
  | [] => None
  | K' :: c' => if kentry_eqb K K' then Some c' else seekK K c'
  end.
Fixpoint ent_walk (kcs : list kentry) (cur : list kentry) (kch : list kentry) : bool :=
  match kch with
  | [] => true
  | K :: rest =>
      match seekK K cur with
      | Some cur' => ent_walk kcs cur' rest
      | None => if existsbL (kentry_eqb K) kcs then ent_walk kcs cur rest else false
      end
  end.
Lemma seekK_sound : ltac2:(zQ "c0!ir7!hm5!jn7!jnd!hq9!p0!hg6!h8!hh3!jo4!joa!jp8>1K$0>1c@1$1$0>2c'@1$1$0>0@3$4@1$7@1$1$0@2$b^3^2@2$5@1$1$0^1@2$3@2$9$0\2K'$0@2$3@3$2$0^1^4@3$4$6@2$a^5^1$8>1x$0>0@3$2$0^1^3@3$2$0^2^5").
Proof.
  intros K c. induction c as [|K1 r IH]; intros c' H; [discriminate|].
  cbn [seekK] in H. destruct (kentry_eqb K K1) eqn:E.
  - injection H as <-. split; [exists K1; split; [left; reflexivity|exact E]|]. intros x Hx. right; exact Hx.
  - destruct (IH c' H) as [[K' [HK' HE]] Hs]. split; [exists K'; split; [right; exact HK'|exact HE]|].
    intros x Hx. right. apply Hs. exact Hx.
Qed.
Lemma ent_walk_eq : ltac2:(zQ "90!ir7!hm5!jn7!hg6!hq9!joa!jq0!ju8!jv4>3kcs@1$1$0>3kch@1$1$0>3cur@1$1$0>0>1x$0>0@3$2$0^1^2@3$2$0^2^5@3$4$3@3$6^4^2^3@3$8$0\1K$0@3$7$0@1$5^1^5^3").
Proof.
  intros kcs kch. induction kch as [|K rest IH]; intros cur Hc; [reflexivity|].
  cbn [ent_walk forallb]. destruct (seekK K cur) as [cur'|] eqn:Hs.
  - destruct (seekK_sound K cur cur' Hs) as [[K' [HK' HE]] Hsub].
    assert (Hex : existsbL (kentry_eqb K) kcs = true).
    { rewrite existsbL_eq. apply (proj2 (existsb_exists _ _)). exists K'. split; [apply Hc; exact HK'|exact HE]. }
    rewrite Hex. cbn [andb]. apply IH. intros x Hx. apply Hc. apply Hsub. exact Hx.
  - destruct (existsbL (kentry_eqb K) kcs); [|reflexivity]. cbn [andb]. apply IH. exact Hc.
Qed.

Local Open Scope lzb_scope.
(* [comment removed for export] *)
Definition entailsF : ltac2:(zQ "20!jvf!hg6>2cs$0>2ch$0$1") := ltac2:(zQ "i40!hg6!hgc!kg6!ne!kh2!hm5!kh9!ki1!ki7!hnb!kj0!kjc!kk5!kl0!kl8!km3!kmd!kn9!ko4!kod!kp8!jvf!kq1!kqd!kr3!kre!hh3!ks7!hld!kt2!kte!ku6!jq0!kv2!lgc!lh3\2cs$h5\2ch$h5M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0@2$i3@1$h7^2@1$h7^1M5\1x@1$5$8$0@1$i1@1$6^1$ha\1s$8\1l@1$5$8$1$1@4$2$3$h8@1$h9@1$6^2@1$h9@1$6^1$1@3$i0@1$7^2@1$7^2@1$7^1$1@4$2$hc$hd@1$f^2@1$f^1$1@4$2@2$9$3$3$h6@1$h2^2@1$h2^1$1@4$2@2$9$3$3$h6@1$e^2@1$e^1$1@2$h8@1$b^2@1$b^1$1@2$hb@1$d^2@1$d^1$1@2$i2@1$h0^2@1$h0^1$1@4$2$he$hf@1$h3^2@1$h3^1$1@2$4@1$h1^2@1$h1^1$1@2$4@1$h4^1@1$h4^2$1@2$4@1$c^2@1$c^1$1@2$4@1$a^2@1$a^1$1").
Local Close Scope lzb_scope.
Lemma entailsF_eq : ltac2:(zQ "50!jvf!hg6!hq9!lha!li5>2cs$0>2ch$0@3$2$1@2$4^2^1@2$3^2^1").
Proof.
  intros cs ch. unfold entailsF, entails.
  rewrite (ent_walk_eq (kn cs) (kn ch) (kn cs) (fun x H => H)). reflexivity.
Qed.
Lemma entailsF_feq : ltac2:(zQ "50!jvf!hg6!hq9!lha!li5@3$2>2cs$0>2ch$0$1$4$3").
Proof. apply functional_extensionality; intros cs. apply functional_extensionality; intros ch. apply entailsF_eq. Qed.


(* [comment removed for export] *)
Definition mmap_nullF : ltac2:(zQ "40!hg6!jvf!h8!lj0>2cs$1>4kind$3>5eager$0>7visible$0@1$2$1") := ltac2:(zQ "j20!ir7!hnb!hsd!jvf!h8!ne!hg6!lj9!lje!km3!lk4!hm5!oa!ki1!lka!ll1!ll8!imd!ihc!p0!o5!lld!lm3!lm8!lmd!ln3!kh9!kp8!lne!lob!lp8!lq2!lr2!lre!ls8!lt7!lu4!lj0!lv4!mg0!mgc!mh9!jm3!mi4!mid!mj3!kre!mjb!mk4!mkb\2cs$3\4kind$i5\5eager$6\7visible$6M4\1x@1$4@2$1@2$1$5$2$2@1$4$3@1$i6^4\1p@2$1@2$1$5$2$2M1\1p@2$1@2$1$5$2$2@1$4$3^1\2p0@2$1$5$2\3nhi$2M1\2p0@2$1$5$2@1$4$3^2\2ne$5\3nlo$2M6\0$6@1$4$3@2$8@2$8@2$8@2$8@2$i0?3nx0^9@2$hf@1$e^9^2@3$i1?1A^9^3@2$h7@1$h5^7@3$hd?5LIMIT^9^3@1$i7@1$9^9=1v$h4@1$e^9=4base$5@2$he+hgg0@1$f^1=6kfacts@1$b$0@3$a$0@3$ib@1$f^2+1@2$j0@2$h1$h9^3+hgg0@3$7$0@3$i8^1^4^3@3$7$0@3$i2?1A^1^4@3$7$0@4$i4?1A@1$9^b^1^4@3$i3@1$9^b^1^4=4kmem@1$b$0@3$a$0@2$ic@2$h0^2Z^5@3$a$0@2$id@2$h0^2Z^5@1$h6$0=2k'@1$b$0@3$7$0^2@2$ia@1$d^d@1$9^d=3cs1$3@8$hc^e@3$if@1$ie@1$ha^eNa^4^1@1$h2^5@3$h8^4^7^d^8^c@2$h1@1$hb^e@2$j1+2^8M6\7visible$6@1$4$3^c@6$i9?1A?5LIMIT^1^5^8@3$7$0^3@1$d^1@2$h3$3^1@1$c$3@1$c$3").

Definition mmap_fixed_grantF : ltac2:(zQ "80!hg6!hsd!jvf!ne!hm5!h8!hld!lj0>2cs$2>3ms0@1$4$6>1b$3>3off$1>2ne$3>3nhi$1>4kind$7>5eager$0>7visible$0@1$5$2") := ltac2:(zQ "i30!ir7!ne!hg6!hm5!jvf!hld!lk4!lm3!lj9!hnb!hsd!ki1!ll8!p0!hp0!h8!ho1!lmd!ml2!kh9!ko4!kp8!lne!lj0!mld!lka!mma!mn1!mh9!mo1!jm3!mid!mj3!kre!mof\2cs$4\3ms0@1$3$5\1b$1\3off$a\2ne$1\3nhi$a\4kind$h7\5eager$2\7visible$2=1k@1$3$0@1$b^9=1a$1@2$ha^aNa=1m$5@3$h1^1^7^5=4kmem@1$3$0@3$6$0@2$hf@2$c^a^9^8@3$6$0@2$i0@2$c^a^9^8@1$7$0=3ksh@1$3$0M2\0$2@1$3$0@2$h8^7$h2@4$i2@2$9$1$1$0\1p@2$9$1$1@5$hb?1A^5@3$6$5^3@1$7$5@3$e$1$1^1@3$h0$1$1^1@1$h4^d@1$7$0=2k'@1$3$0@3$8$0^1@2$he^5^d=3cs1$4@8$h6@2$hd^f^e@1$i1@1$h3^f^1@1$h9^f^4^a^8@1$h5^fM2\7visible$2@1$f$4^8@6$hc?1A?5LIMIT^1^6^c@3$8$0^4@1$b^1@2$d$4^1").

Definition mmap_fixed_freeF : ltac2:(zQ "40!hg6!jvf!h8!lj0>2cs$1>4kind$3>5eager$0>7visible$0@1$2$1") := ltac2:(zQ "i16!hnb!hsd!ne!h8!jvf!lje!hld!hg6!km3!oa!lq2!lka!lld!lm8!hgc!hm5!ina!mpb!lob!mq5!mr3!ms8!jv4!mt9!ii7!mu1!mue!ki1!lj0!mv9!mma!ng3!ir7&@2$0@2$0@2$0@2$0$2$1$2$1$1&@1$3~0&\1x~1@1$3$4&\1p~0@1$3$4&\2p0@2$0@2$0@2$0$2$1$2$1@1$3$4&\2p1@2$0@2$0$2$1$2@1$3$4\2cs$4\4kind$hc\5eager$7\7visible$7=1k@1$f$i0@1$hb^4=1a$2@2$he^5NaM3~2@4$h3?1A^6$h8$e\1p~0M0~3^1\2p0@2$0@2$0@2$0$2$1$2$1\3nhi$1M0~4^2\2p1@2$0@2$0$2$1$2\3nlo$1M0~5^2\2p2@2$0$2$1\2ne$2M0\2p2@2$0$2$1@1$3$4^2\1b$2\3off$1M7\0$7@1$3$4@2$5@2$5@2$5@2$5@1$hd@1$8^f@3$h6$6\1m$6@7$h5^c^3^2^4@1$h0^1Z@1$h1^1@1$8^f@2$d@1$c^d@3$h2?5LIMIT^f^7@2$a@1$b^f^3@2$a@1$b^f^a@9$h4^f@1$8^f^2^1^3^7^e^d^c@1$9$4M3~2@4$h3?1A^6$h7$e\1p~0M0~3^1\2p0@2$0@2$0@2$0$2$1$2$1\3nhi$1M0~4^2\2p1@2$0@2$0$2$1$2\3nlo$1M0~5^2\2p2@2$0$2$1\2ne$2M0\2p2@2$0$2$1@1$3$4^2\1b$2\3off$1M3\1x@1$3$6@1$3$4@4$h9^b@1$8^f^a^3\1h$6=3ms0@1$f$6@2$hf@1$8^h0^1M7\0$7@1$3$4@2$5@2$5@2$5@3$h6$6\1m$6@2$d@1$c@1$ha^1@7$h5^e^5^4^6@1$h0^1Z@1$h1^1^1@2$d@1$c^f@3$h2?5LIMIT^h1^9@2$a@1$b^h1^5@2$a@1$b^h1^c@9$h4^h1^1^4^3^5^9^h0^f^e@1$9$4@1$9$4@1$9$4").

Definition node_mmap2F : ltac2:(zQ "30!jvf!h8!hnb>2cs$0@1$1@2$2$0$0") := ltac2:(zQ "h30!ngd!jvf!oa!h8!hsd!hnb!hgc!hg6!nh8!hh3!nic!nj9!ml2!nk6!nkf!p0!in4!nl6!nm3\2cs$1M3\1x@1$3@2$5@2$5$4$4$7@1$3@2$5$1$1@1$h1^1\1p@2$5@2$5$4$4$7M5\1p@2$5@2$5$4$4$7@1$3@2$5$1$1^1\2p0@2$5$4$4\6isnull$7M5\2p0@2$5$4$4@1$3@2$5$1$1^2\4prot$4\5flags$4=1g@1$3$1M7\6isnull$7@1$3$1^3M4\4prot$4@1$3$1^2M4\5flags$4@1$3$1^1@1$2$1\1p$0M0\1p$0@1$3$1^1\2p0$0@1$2$1\2p0$0M0\2p0$0@1$3$1^1\2p1$0M0\2p1$0@1$3$1^1\2p2$0@1$2$1\2p2$0M0\2p2$0@1$3$1^1\2p3$0@1$2$1\2p3$0M0\2p3$0@1$3$1^1\2p4$0@1$2$1\2p4$0M0\2p4$0@1$3$1^1\2p5$0M0\2p5$0@1$3$1^1\2p6$0@1$2$1\2p6$0M0\2p6$0@1$3$1^1\2p7$0@1$2$1\2p7$0M0\2p7$0@1$3$1^1\2p8$0@1$2$1\2p8$0M0\2p8$0@1$3$1^1\2p9$0@1$2$1\2p9$0M0\2p9$0@1$3$1^1\3p10$0@1$2$1\3p10$0M0\3p10$0@1$3$1^1\3p11$0@1$2$1\3p11$0M0\3p11$0@1$3$1^1\3p12$0@1$2$1\3p12$0M0\3p12$0@1$3$1^1\3p13$0@1$2$1\3p13$0M0\3p13$0@1$3$1^1\3p14$0@1$2$1\3p14$0@1$2$1@4$a^h5$b$6$6@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\2p5$0@1$2$1@4$a^c$d$6$6@1$2$1@1$2$1@1$2$1\2p1$0@1$2$1@1$2$1@1$2$1\1p$0@1$2$1\1p$0M0\1p$0@1$3$1^1\2p0$0M0\2p0$0@1$3$1^1\2p1$0@1$2$1\2p1$0@1$2$1M4\5flags$4@1$3$1^3@1$2$1\2p1$0M0\2p1$0@1$3$1^1\2p2$0@1$2$1\2p2$0M0\2p2$0@1$3$1^1\2p3$0M0\2p3$0@1$3$1^1\2p4$0@1$2$1\2p4$0M0\2p4$0@1$3$1^1\2p5$0@1$2$1\2p5$0M0\2p5$0@1$3$1^1\2p6$0@1$2$1\2p6$0M0\2p6$0@1$3$1^1\2p7$0M0\2p7$0@1$3$1^1\2p8$0@1$2$1\2p8$0M0\2p8$0@1$3$1^1\2p9$0@1$2$1\2p9$0M0\2p9$0@1$3$1^1\3p10$0@1$2$1\3p10$0M0\3p10$0@1$3$1^1\3p11$0@1$2$1\3p11$0M0\3p11$0@1$3$1^1\3p12$0@1$2$1\3p12$0M0\3p12$0@1$3$1^1\3p13$0@1$2$1\3p13$0M0\3p13$0@1$3$1^1\3p14$0@1$2$1\3p14$0M0\3p14$0@1$3$1^1\3p15$0@1$2$1\3p15$0M0\3p15$0@1$3$1^1\3p16$0@1$2$1\3p16$0@1$2$1@4$a^h7$c$6$9@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\2p7$0@1$2$1@4$a^e$e$9$9@1$2$1@1$2$1@1$2$1\2p3$0@1$2$1@1$2$1@1$2$1\2p1$0@1$2$1\2p0$0@1$2$1@1$2$1\1p$0@1$2$1M4\4prot$4@1$3$1^2M4\5flags$4@1$3$1^1@1$2$1\1p$0M0\1p$0@1$3$1^1\2p0$0@1$2$1\2p0$0M0\2p0$0@1$3$1^1\2p1$0M0\2p1$0@1$3$1^1\2p2$0@1$2$1\2p2$0M0\2p2$0@1$3$1^1\2p3$0@1$2$1\2p3$0M0\2p3$0@1$3$1^1\2p4$0M0\2p4$0@1$3$1^1\2p5$0M0\2p5$0@1$3$1^1\2p6$0@1$2$1\2p6$0M0\2p6$0@1$3$1^1\2p7$0@1$2$1\2p7$0M0\2p7$0@1$3$1^1\2p8$0@1$2$1\2p8$0M0\2p8$0@1$3$1^1\2p9$0@1$2$1\2p9$0M0\2p9$0@1$3$1^1\3p10$0@1$2$1\3p10$0M0\3p10$0@1$3$1^1\3p11$0@1$2$1\3p11$0M0\3p11$0@1$3$1^1\3p12$0@1$2$1\3p12$0M0\3p12$0@1$3$1^1\3p13$0@1$2$1\3p13$0M0\3p13$0@1$3$1^1\3p14$0@1$2$1\3p14$0@1$2$1@4$8^h5$b$6$6@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\2p5$0@1$2$1@4$8^c$d$6$6\2p4$0M0\2p4$0@1$3$1^1\2p5$0M0\2p5$0@1$3$1^1\2p6$0@1$2$1\2p6$0M0\2p6$0@1$3$1^1\2p7$0@1$2$1\2p7$0M0\2p7$0@1$3$1^1\2p8$0@1$2$1\2p8$0M0\2p8$0@1$3$1^1\2p9$0@1$2$1\2p9$0M0\2p9$0@1$3$1^1\3p10$0@1$2$1\3p10$0M0\3p10$0@1$3$1^1\3p11$0@1$2$1\3p11$0M0\3p11$0@1$3$1^1\3p12$0@1$2$1\3p12$0M0\3p12$0@1$3$1^1\3p13$0@1$2$1\3p13$0M0\3p13$0@1$3$1^1\3p14$0M0\3p14$0@1$3$1^1\3p15$0@1$2$1\3p15$0M0\3p15$0@1$3$1^1\3p16$0@1$2$1\3p16$0M0\3p16$0@1$3$1^1\3p17$0@1$2$1\3p17$0M0\3p17$0@1$3$1^1\3p18$0@1$2$1\3p18$0M0\3p18$0@1$3$1^1\3p19$0@1$2$1\3p19$0M0\3p19$0@1$3$1^1\3p20$0@1$2$1\3p20$0@1$2$1@4$8^hb$b$6$6@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\3p14$0@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\2p5$0@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\2p1$0@1$2$1@1$2$1@1$2$1\1p$0@1$2$1\1p$0M0\1p$0@1$3$1^1\2p0$0M0\2p0$0@1$3$1^1\2p1$0@1$2$1\2p1$0@1$2$1M4\5flags$4@1$3$1^3@1$2$1\2p1$0M0\2p1$0@1$3$1^1\2p2$0@1$2$1\2p2$0M0\2p2$0@1$3$1^1\2p3$0M0\2p3$0@1$3$1^1\2p4$0@1$2$1\2p4$0M0\2p4$0@1$3$1^1\2p5$0@1$2$1\2p5$0M0\2p5$0@1$3$1^1\2p6$0M0\2p6$0@1$3$1^1\2p7$0M0\2p7$0@1$3$1^1\2p8$0@1$2$1\2p8$0M0\2p8$0@1$3$1^1\2p9$0@1$2$1\2p9$0M0\2p9$0@1$3$1^1\3p10$0@1$2$1\3p10$0M0\3p10$0@1$3$1^1\3p11$0@1$2$1\3p11$0M0\3p11$0@1$3$1^1\3p12$0@1$2$1\3p12$0M0\3p12$0@1$3$1^1\3p13$0@1$2$1\3p13$0M0\3p13$0@1$3$1^1\3p14$0@1$2$1\3p14$0M0\3p14$0@1$3$1^1\3p15$0@1$2$1\3p15$0M0\3p15$0@1$3$1^1\3p16$0@1$2$1\3p16$0@1$2$1@4$8^h7$c$6$6@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\2p7$0@1$2$1@4$8^e$e$9$9\2p6$0M0\2p6$0@1$3$1^1\2p7$0M0\2p7$0@1$3$1^1\2p8$0@1$2$1\2p8$0M0\2p8$0@1$3$1^1\2p9$0@1$2$1\2p9$0M0\2p9$0@1$3$1^1\3p10$0@1$2$1\3p10$0M0\3p10$0@1$3$1^1\3p11$0@1$2$1\3p11$0M0\3p11$0@1$3$1^1\3p12$0@1$2$1\3p12$0M0\3p12$0@1$3$1^1\3p13$0@1$2$1\3p13$0M0\3p13$0@1$3$1^1\3p14$0@1$2$1\3p14$0M0\3p14$0@1$3$1^1\3p15$0@1$2$1\3p15$0M0\3p15$0@1$3$1^1\3p16$0M0\3p16$0@1$3$1^1\3p17$0@1$2$1\3p17$0M0\3p17$0@1$3$1^1\3p18$0@1$2$1\3p18$0M0\3p18$0@1$3$1^1\3p19$0@1$2$1\3p19$0M0\3p19$0@1$3$1^1\3p20$0@1$2$1\3p20$0M0\3p20$0@1$3$1^1\3p21$0@1$2$1\3p21$0M0\3p21$0@1$3$1^1\3p22$0@1$2$1\3p22$0@1$2$1@4$8^hd$c$6$6@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\3p16$0@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\2p7$0@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\2p3$0@1$2$1@1$2$1@1$2$1\2p1$0@1$2$1\2p0$0@1$2$1@1$2$1\1p$0@1$2$1M3\1g@1$3$1@1$3@2$5$1$1^1\3csG$1@2$f@2$5$1$1@4$h0$1$1@1$h2^8^1@1$2@2$5$1$1@1$2@2$5$1$1").

Definition node_mmapgapsF : ltac2:(zQ "30!jvf!hm5!h8>2cs$0@1$2@1$1$0") := ltac2:(zQ "j60!hm5!jvf!ngd!hsd!h8!oa!hnb!ir7!hg6!ne!lj9!lje!km3!lk4!ki1!lka!ll1!ll8!imd!ihc!o5!lm3!hh3!hs6!lmd!ln3!nkf!kh9!kp8!lne!lob!lp8!lq2!lr2!nmd!lre!nna!ls8!lt7!lu4!nl6!lv4!mg0!mgc!no5!mh9!jm3!mi4!mid!mj3!kre!mjb!mk4!mkb\2cs$1M4\1x@1$4@2$6@2$6$3$3$8@1$4@1$0$1@1$i8^1\1p@2$6@2$6$3$3$8M6\1p@2$6@2$6$3$3$8@1$4@1$0$1^1\2p0@2$6$3$3\1b$8M6\2p0@2$6$3$3@1$4@1$0$1^2\1z$3\2z0$3M3\1z$3@1$4@1$0$1^2@1$5@1$0$1\2p1$2M2\2p1$2@1$4@1$0$1^1\2p2$2M2\2p2$2@1$4@1$0$1^1\2p3$2@1$5@1$0$1\2p3$2@1$5@1$0$1M3\2z0$3@1$4@1$0$1^3@1$5@1$0$1\2p3$2M2\2p3$2@1$4@1$0$1^1\2p4$2@1$5@1$0$1\2p4$2M2\2p4$2@1$4@1$0$1^1\2p5$2M2\2p5$2@1$4@1$0$1^1\2p6$2@1$5@1$0$1\2p6$2M2\2p6$2@1$4@1$0$1^1\2p7$2@1$5@1$0$1\2p7$2M2\2p7$2@1$4@1$0$1^1\2p8$2@1$5@1$0$1\2p8$2M2\2p8$2@1$4@1$0$1^1\2p9$2@1$5@1$0$1\2p9$2@1$5@1$0$1M8\1b$8@1$4@1$0$1^bM4\1x@1$4@2$6@2$6$9$3$3@1$4@1$0$1@1$i9^e\2p9@2$6@2$6$9$3$3M6\2p9@2$6@2$6$9$3$3@1$4@1$0$1^1\3p10@2$6$9$3\3nhi$3M6\3p10@2$6$9$3@1$4@1$0$1^2\2ne$9\3nlo$3M8\0$8@1$4@1$0$1@2$b@2$b@2$b@2$b@2$i1?3nx0^h3@2$i0@1$f^h3^2@3$i3?1A^h3^3@3$he?5LIMIT^h3^3@1$ia@1$c^h3=1v$h4@1$f^h3=4base$9@2$hf+hgg0@1$h0^1=6kfacts@1$0$7@3$d$7@3$if@1$h0^2+1@2$j4@2$h2$h9^3+hgg0@3$a$7@3$ib^1^4^3@3$a$7@3$i5?1A^1^4@3$a$7@4$i7?1A@1$c^h5^1^4@3$i6@1$c^h5^1^4=4kmem@1$0$7@3$d$7@2$j0@2$h1^2Z^5@3$d$7@2$j1@2$h1^2Z^5@1$h5$7=2k'@1$0$7@3$a$7^2@2$ie@1$e^h7@1$c^h7=3cs1$1@8$hd^h8@3$j3@1$j2@1$hb^h8Na^4^1@1$h3^5@3$h8^4^7$ha^8$h6@2$h2@1$hc^h8@2$j5+2^8M4\1x@1$4@1$0@2$6$3$3@1$4@1$0$1@3$i4^1^6+hgg0\4gaps@1$0@2$6$3$3@2$ic$1@4$h7@2$6$3$3@1$4$1\1g@2$6$3$3=3csg$1@3$i2^3^8^1@6$id?1A?5LIMIT^1^8^b@3$a$7^6@1$e^1^1@1$5@1$0$1@1$5@1$0$1@1$5@1$0$1@1$5@1$0$1@1$5@1$0$1@1$5@1$0$1@1$5@1$0$1\2p5$2@1$5@1$0$1@1$5@1$0$1@1$5@1$0$1\2p3$2@1$5@1$0$1\2p2$2@1$5@1$0$1@1$5@1$0$1\2p1$2@1$5@1$0$1@1$5@1$0$1").

(* [comment removed for export] *)
Lemma mmap_nullF_eq : ltac2:(zQ "70!hg6!jvf!h8!hq9!lj0!np0!nic@3$3>2cs$1>4kind$4>5eager$0>7visible$0@1$2$1$6@3$5?1A?3nx0?5LIMIT").
Proof. unfold mmap_nullF, mmap_null. rewrite kn_grant_filterF_feq. reflexivity. Qed.
Lemma mmap_fixed_grantF_eq : ltac2:(zQ "b0!hg6!hsd!jvf!ne!hm5!h8!hq9!hld!lj0!npd!mr3@3$6>2cs$2>3ms0@1$4$7>1b$3>3off$1>2ne$3>3nhi$1>4kind$8>5eager$0>7visible$0@1$5$2$a@2$9?1A?5LIMIT").
Proof. unfold mmap_fixed_grantF, mmap_fixed_grant. rewrite kn_grant_filterF_feq. reflexivity. Qed.
Lemma mmap_fixed_freeF_eq : ltac2:(zQ "70!hg6!jvf!h8!hq9!lj0!nr2!nh8@3$3>2cs$1>4kind$4>5eager$0>7visible$0@1$2$1$6@2$5?1A?5LIMIT").
Proof. unfold mmap_fixed_freeF, mmap_fixed_free. rewrite mmap_fixed_grantF_eq. reflexivity. Qed.
Lemma node_mmap2F_eq : ltac2:(zQ "60!jvf!h8!hnb!hq9!ns5!nt3@3$3>2cs$0@1$1@2$2$0$0$5@3$4?1A?3nx0?5LIMIT").
Proof. unfold node_mmap2F, node_mmap2. rewrite mmap_nullF_eq, mmap_fixed_freeF_eq. reflexivity. Qed.
Lemma node_mmapgapsF_eq : ltac2:(zQ "60!jvf!hm5!h8!hq9!nu1!nv2@3$3>2cs$0@1$2@1$1$0$5@3$4?1A?3nx0?5LIMIT").
Proof. unfold node_mmapgapsF, node_mmapgaps. rewrite kn_grant_filterF_feq. reflexivity. Qed.


Section Check.
Variable XN : ltac2:(zQ "50!jvf!hm5!o5!h8!ne>0$2>0@1$1$4>0$0@1$3$0").
Variable XE : ltac2:(zQ "80!hm5!hnb!jvf!o5!h8!hsd!ol4!ne>0$3>0@1$0$7>0$2@1$4@2$1@2$1$5@1$0$6$2").
Variable XB : ltac2:(zQ "60!jvf!hm5!o5!h8!hnb!ne>0$2>0@1$1$5>0$0@1$3@2$4$0$0").
Variable HS : ltac2:(zQ "30!o5!h8!jvf>0$0@1$1$2").
Variable KC : nat.
Variable bfuel : nat.

Fixpoint check_f (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) {struct fuel} : cres :=
  match fuel with
  | O => CErr 0 p cs
  | S f =>
  let check_in := check_f in
  let check (f : nat) := check_in f lc in
  (* [comment removed for export] *)
  let gcb := match lc with Some c => lc_bnd c | None => nx0 end in
  if negb match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end then CErr 9 p cs else
  match p with
  | PRun stops k =>
      match run_block_gc segs IT gcb KC bfuel (stops ++ STOPS A) cs with
      | Some cs' => check f cs' k
      | None => CErr 1 p cs
      end
  | PSplit e mid k1 k2 =>
      if expr_vars_lt nx0 e then
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            match check f (set_kn cs (KRange e lo mid :: kn cs)) k1 with
            | COk s1 =>
                match check f (set_kn cs (KRange e (mid + 1) hi :: kn cs)) k2 with
                | COk s2 => COk (SCase e mid s1 s2)
                | err => err
                end
            | err => err
            end
          else (* [comment removed for export] *)
            if Z.leb hi mid then check f cs k1 else check f cs k2
      | None => CErr 3 p cs
      end
      else CErr 3 p cs
  | PCase2 e mid k1 k2 =>
      match erange (kn cs) e with
      | Some (lo, hi) =>
          if negb (Z.leb lo mid && Z.ltb mid hi)%bool then (if Z.leb hi mid then check f cs k1 else check f cs k2) else
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            let cs1 := set_kn cs (KRange e lo mid :: kn cs) in
            let cs2 := set_kn cs (KRange e (mid + 1) hi :: kn cs) in
            (* [comment removed for export] *)
            if kn_contra (kn cs1) then check f cs2 k2
            else if kn_contra (kn cs2) then check f cs1 k1
            else
            match check f cs1 k1 with
            | COk s1 =>
                match check f cs2 k2 with
                | COk s2 => if shape_eqb_h s1 s2 then COk s1 else CErr 6 p cs
                | err => err
                end
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PCaseGaps v sc ks =>
      match node_casegaps cs v sc with
      | Some css => casegaps_fold (check f) p cs css ks None
      | None => CErr 3 p cs
      end
  | PRangeGaps v sc k => match node_rangegaps cs v sc with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PMmapGaps ks =>
      if is_ecall_at segs cs then
        match node_mmapgapsF cs with
        | Some css => casegaps_fold (check f) p cs css ks None
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PFrozen _ hs ws cold items k =>
      match lc with
      | Some _ => CErr 8 p cs
      | None => match (node_frozen segs IT A nx0) KC bfuel hs ws cold items cs with Some cs' => check f cs' k | None => CErr 1 p cs end
      end
  | PCaseDisj b1 b2 k1 k2 =>
      match node_casedisj cs b1 b2 with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk s1 => match check f csb k2 with
                      | COk s2 => if shape_eqb_h s1 s2 then COk s1 else CErr 6 p cs
                      | err => err
                      end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PShDisj b1 n1 b2 n2 k => match node_shdisj A cs b1 n1 b2 n2 with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PContra => if kn_contra (kn cs) then COk SNil else CErr 3 p cs
  | PFact K k => if fact_ok (kn cs) K then check f (add_kn cs [K]) k else CErr 3 p cs
  | PJoin b off n k => match node_join segs cs b off n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PForget ixs k => check f (set_kn cs (drop_ixs ixs 0 (kn cs))) k
  | PDropRange b n k => check f (node_droprange cs b n) k
  | PGcKeep ws k => check f (set_kn cs (kn_keep (kn cs) ws)) k
  | PBump m k => match node_bump cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavoc rs k => match node_havoc nx0 cs rs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBig K k => match node_havocbig nx0 cs K with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFresh r logc base k => match node_fresh nx0 cs r logc base with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PSys y k =>
      if is_ecall_at segs cs then
        match (node_sys A nx0) y cs with Some cs' => check f cs' k | None => CErr 3 p cs end
      else CErr 2 p cs
  | PBrk2 ka kb =>
      (* [comment removed for export] *)
      if is_ecall_at segs cs then
        match node_brk2 A LIMIT cs with
        | Some (csa, csb) =>
            match check f csa ka with
            | COk sa => match check f csb kb with
                        | COk sb => if shape_eqb_h sa sb then COk sa else CErr 6 p cs
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmap1 kb =>
      if is_ecall_at segs cs then
        match node_mmap2F cs with
        | Some (_, csb) => check f csb kb
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PMmapIn1 kb =>
      if is_ecall_at segs cs then
        match node_mmapin1 A LIMIT cs with
        | Some csb => check f csb kb
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PNameCell b n k => match node_namecell segs nx0 cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PMprotect1 kb =>
      if is_ecall_at segs cs then
        match node_mprotect A LIMIT cs with
        | Some csb => check f csb kb
        | None => CErr 3 p cs
        end
      else CErr 2 p cs
  | PX x args k => match (node_x segs A nx0) x args cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PExt id args k => match XN id args cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PEmit id args k =>
      match XE id args cs with
      | Some (fd, ps, cs') => match check f cs' k with COk s => COk (SEmitP fd ps s) | err => err end
      | None => CErr 3 p cs
      end
  | PExt2 id args k1 k2 =>
      match XB id args cs with
      | Some (csa, csb) =>
          match check f csa k1 with
          | COk sa => match check f csb k2 with COk sb => COk (SAlt2 sa sb) | err => err end
          | err => err
          end
      | None => CErr 3 p cs
      end
  | PLoop J N inv body k =>
      match loop_ok nx0 cs J N inv with
      | Some nhi =>
          let lo := S J in let hi := nxt inv in
          if (Z.eqb (pc inv) (pc cs) && entails_h A lo hi cs (inst inv J (ELit 0)))%bool then
            match check_in f (Some (LC (pc cs) (inst inv J (eaddz (EVar J) 1)) lo hi)) (loop_body_state J N nhi inv) body with
            | COk SNext => check f (inst inv J N) k
            | COk _ => CErr 7 p cs
            | err => err
            end
          else CErr 3 p cs
      | None => CErr 3 p cs
      end
  | PNext =>
      match lc with
      | Some (LC h nx lo hi) =>
          if (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool then COk SNext else CErr 3 p cs
      | _ => CErr 8 p cs
      end
  | PHandoff h =>
      match HS h with
      | Some ch => if entailsF cs ch then COk (SHole h) else CErr 3 p cs
      | None => CErr 4 p cs
      end
  | PExit =>
      if is_ecall_at segs cs then
        match node_exit cs with Some code => COk (SExit code) | None => CErr 3 p cs end
      else CErr 2 p cs
  | PSpin => CErr 2 p cs   (* [comment removed for export] *)
  | PFog i sz k => match node_fog cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PFogNew i sz k => match node_fognew cs i sz with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PGhost b n k => match node_ghost LIMIT cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PUnvis b n k => match node_unvis A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocBrk lo hi k => match node_havocbrk nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PIntro lo hi k => match node_intro nx0 cs lo hi with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRename m k => match node_rename gcb cs m with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PCompact k => match node_compact gcb cs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PVia j js lo karms k =>
      if via_ok nx0 cs js lo then
        match check f js k with
        | COk sk => check_in f (Some (JC j js sk (nxt cs) lo)) cs karms
        | err => err
        end
      else CErr 3 p cs
  | PMerge j =>
      match lc with
      | Some (JC j' js sk b lo) =>
          if (Nat.eqb j j' && Z.eqb (pc cs) (pc js) && shape_vars_lt nx0 sk && entails_h A lo (nxt js) cs js)%bool
          then COk sk else CErr 3 p cs
      | _ => CErr 8 p cs
      end
  | PAbstractCell b n k => match node_abstractcell A cs b n with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PHavocWords bs k => match node_havocwords nx0 cs bs with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PRespell r e k => match node_respell cs r e with Some cs' => check f cs' k | None => CErr 3 p cs end
  | PDiamond joinpc rs k =>
      match branch_probe IT cs with
      | Some e =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              (* [comment removed for export] *)
              if (Z.ltb hi 1 || Z.ltb 0 lo)%bool then
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs with
                | Some cs' => if Z.eqb (pc cs') joinpc then check f cs' k else CErr 3 p cs'
                | None => CErr 1 p cs
                end
              else
                let cs1 := set_kn cs (KRange e lo 0 :: kn cs) in
                let cs2 := set_kn cs (KRange e 1 hi :: kn cs) in
                match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs1 with
                | Some ca =>
                    match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs2 with
                    | Some cb =>
                        match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                        | Some csj => check f csj k
                        | None => CErr 3 p ca    (* [comment removed for export] *)
                        end
                    | None => CErr 1 p cs2
                    end
                | None => CErr 1 p cs1
                end
          | None => CErr 3 p cs
          end
      | None => CErr 2 p cs                  (* [comment removed for export] *)
      end
  end
  end.

(* [comment removed for export] *)
Let check := check segs IT A nx0 LIMIT XN XE XB HS KC bfuel.

Theorem check_f_eq : forall fuel lc cs p, check_f fuel lc cs p = check fuel lc cs p.
Proof.
  induction fuel as [|f IH]; intros lc cs p; [reflexivity|].
  assert (IHf : check_f f = check f).
  { apply functional_extensionality; intros lc'. apply functional_extensionality; intros cs'.
    apply functional_extensionality; intros p'. apply IH. }
  cbn [check_f]. unfold check. cbn [AP.check]. fold check.
  rewrite IHf, node_mmap2F_eq, node_mmapgapsF_eq, entailsF_feq. reflexivity.
Qed.

Corollary check_of_f : forall fuel lc cs p s, check_f fuel lc cs p = COk s -> check fuel lc cs p = COk s.
Proof. intros fuel lc cs p s H. rewrite <- check_f_eq. exact H. Qed.

End Check.
End WithSegs.
End FC.
