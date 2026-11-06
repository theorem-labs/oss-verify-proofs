(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCStream.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDState.

Module BzDHuff.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BZ_MAX_CODE_LEN : Z := 23.

(* [comment removed for export] *)
Fixpoint hbd_permJ (n : nat) (j : Z) (i : Z) (len perm : zarr) (off pp : Z) : zarr * Z :=
  match n with
  | O => (perm, pp)
  | S n' => if zget len (off + j) =? i
            then hbd_permJ n' (j + 1) i len (zset perm (off + pp) j) off (pp + 1)
            else hbd_permJ n' (j + 1) i len perm off pp
  end.
(* [comment removed for export] *)
Fixpoint hbd_permI (n : nat) (i : Z) (len perm : zarr) (off pp alphaSize : Z) : zarr * Z :=
  match n with
  | O => (perm, pp)
  | S n' => let '(perm', pp') := hbd_permJ (Z.to_nat alphaSize) 0 i len perm off pp in
            hbd_permI n' (i + 1) len perm' off pp' alphaSize
  end.
(* [comment removed for export] *)
Fixpoint hbd_zero (n : nat) (i : Z) (a : zarr) (off : Z) : zarr :=
  match n with O => a | S n' => hbd_zero n' (i + 1) (zset a (off + i) 0) off end.
(* [comment removed for export] *)
Fixpoint hbd_count (n : nat) (i : Z) (len base : zarr) (off : Z) : zarr :=
  match n with
  | O => base
  | S n' => hbd_count n' (i + 1) len (zincr base (off + zget len (off + i) + 1)) off
  end.
(* [comment removed for export] *)
Fixpoint hbd_accum (n : nat) (i : Z) (base : zarr) (off : Z) : zarr :=
  match n with
  | O => base
  | S n' => hbd_accum n' (i + 1) (zset base (off + i) (zget base (off + i) + zget base (off + i - 1))) off
  end.
(* [comment removed for export] *)
Fixpoint hbd_limit (n : nat) (i : Z) (base limit : zarr) (off vec : Z) : zarr * Z :=
  match n with
  | O => (limit, vec)
  | S n' => let vec1 := vec + (zget base (off + i + 1) - zget base (off + i)) in
            hbd_limit n' (i + 1) base (zset limit (off + i) (vec1 - 1)) off (2 * vec1)
  end.
(* [comment removed for export] *)
Fixpoint hbd_base (n : nat) (i : Z) (limit base : zarr) (off : Z) : zarr :=
  match n with
  | O => base
  | S n' => hbd_base n' (i + 1) limit (zset base (off + i) (2 * (zget limit (off + i - 1) + 1) - zget base (off + i))) off
  end.

(* [comment removed for export] *)
Definition zspan (lo hi : Z) : nat := Z.to_nat (hi - lo + 1).

(* [comment removed for export] *)
Definition hbCreateDecodeTables (limit base perm len : zarr) (off minLen maxLen alphaSize : Z)
  : zarr * zarr * zarr :=
  let '(perm1, _) := hbd_permI (zspan minLen maxLen) minLen len perm off 0 alphaSize in
  let base1 := hbd_zero (Z.to_nat BZ_MAX_CODE_LEN) 0 base off in
  let base2 := hbd_count (Z.to_nat alphaSize) 0 len base1 off in
  let base3 := hbd_accum (Z.to_nat (BZ_MAX_CODE_LEN - 1)) 1 base2 off in
  let limit1 := hbd_zero (Z.to_nat BZ_MAX_CODE_LEN) 0 limit off in
  let '(limit2, _) := hbd_limit (zspan minLen maxLen) minLen base3 limit1 off 0 in
  let base4 := hbd_base (zspan (minLen + 1) maxLen) (minLen + 1) limit2 base3 off in
  (limit2, base4, perm1).

(* [comment removed for export] *)
(* [comment removed for export] *)
End BzDHuff.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rNums_list : list Z :=
  [619; 720; 127; 481; 931; 816; 813; 233; 566; 247; 985; 724; 205; 454; 863; 491;
   741; 242; 949; 214; 733; 859; 335; 708; 621; 574; 73; 654; 730; 472; 419; 436;
   278; 496; 867; 210; 399; 680; 480; 51; 878; 465; 811; 169; 869; 675; 611; 697;
   867; 561; 862; 687; 507; 283; 482; 129; 807; 591; 733; 623; 150; 238; 59; 379;
   684; 877; 625; 169; 643; 105; 170; 607; 520; 932; 727; 476; 693; 425; 174; 647;
   73; 122; 335; 530; 442; 853; 695; 249; 445; 515; 909; 545; 703; 919; 874; 474;
   882; 500; 594; 612; 641; 801; 220; 162; 819; 984; 589; 513; 495; 799; 161; 604;
   958; 533; 221; 400; 386; 867; 600; 782; 382; 596; 414; 171; 516; 375; 682; 485;
   911; 276; 98; 553; 163; 354; 666; 933; 424; 341; 533; 870; 227; 730; 475; 186;
   263; 647; 537; 686; 600; 224; 469; 68; 770; 919; 190; 373; 294; 822; 808; 206;
   184; 943; 795; 384; 383; 461; 404; 758; 839; 887; 715; 67; 618; 276; 204; 918;
   873; 777; 604; 560; 951; 160; 578; 722; 79; 804; 96; 409; 713; 940; 652; 934;
   970; 447; 318; 353; 859; 672; 112; 785; 645; 863; 803; 350; 139; 93; 354; 99;
   820; 908; 609; 772; 154; 274; 580; 184; 79; 626; 630; 742; 653; 282; 762; 623;
   680; 81; 927; 626; 789; 125; 411; 521; 938; 300; 821; 78; 343; 175; 128; 250;
   170; 774; 972; 275; 999; 639; 495; 78; 352; 126; 857; 956; 358; 619; 580; 124;
   737; 594; 701; 612; 669; 112; 134; 694; 363; 992; 809; 743; 168; 974; 944; 375;
   748; 52; 600; 747; 642; 182; 862; 81; 344; 805; 988; 739; 511; 655; 814; 334;
   249; 515; 897; 955; 664; 981; 649; 113; 974; 459; 893; 228; 433; 837; 553; 268;
   926; 240; 102; 654; 459; 51; 686; 754; 806; 760; 493; 403; 415; 394; 687; 700;
   946; 670; 656; 610; 738; 392; 760; 799; 887; 653; 978; 321; 576; 617; 626; 502;
   894; 679; 243; 440; 680; 879; 194; 572; 640; 724; 926; 56; 204; 700; 707; 151;
   457; 449; 797; 195; 791; 558; 945; 679; 297; 59; 87; 824; 713; 663; 412; 693;
   342; 606; 134; 108; 571; 364; 631; 212; 174; 643; 304; 329; 343; 97; 430; 751;
   497; 314; 983; 374; 822; 928; 140; 206; 73; 263; 980; 736; 876; 478; 430; 305;
   170; 514; 364; 692; 829; 82; 855; 953; 676; 246; 369; 970; 294; 750; 807; 827;
   150; 790; 288; 923; 804; 378; 215; 828; 592; 281; 565; 555; 710; 82; 896; 831;
   547; 261; 524; 462; 293; 465; 502; 56; 661; 821; 976; 991; 658; 869; 905; 758;
   745; 193; 768; 550; 608; 933; 378; 286; 215; 979; 792; 961; 61; 688; 793; 644;
   986; 403; 106; 366; 905; 644; 372; 567; 466; 434; 645; 210; 389; 550; 919; 135;
   780; 773; 635; 389; 707; 100; 626; 958; 165; 504; 920; 176; 193; 713; 857; 265;
   203; 50; 668; 108; 645; 990; 626; 197; 510; 357; 358; 850; 858; 364; 936; 638].
Definition rNums (i : Z) : Z := nth (Z.to_nat i) rNums_list 0.

(* [comment removed for export] *)
Definition rand_upd (d : dst) : dst :=
  let d1 := if d_rNToGo d =? 0
            then d_set_rTPos (d_set_rNToGo d (rNums (d_rTPos d)))
                             (if d_rTPos d + 1 =? 512 then 0 else d_rTPos d + 1)
            else d in
  d_set_rNToGo d1 (d_rNToGo d1 - 1).
(* [comment removed for export] *)
Definition rand_mask (d : dst) : Z := if d_rNToGo d =? 1 then 1 else 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition get_ll4 (d : dst) (i : Z) : Z :=
  Z.land (Z.shiftr (zget (d_ll4 d) (Z.shiftr i 1)) (Z.land (Z.shiftl i 2) 4)) 15.
Definition get_ll (d : dst) (i : Z) : Z := Z.lor (zget (d_ll16 d) i) (Z.shiftl (get_ll4 d i) 16).
Definition set_ll4 (d : dst) (i n : Z) : dst :=
  let k := Z.shiftr i 1 in
  let old := zget (d_ll4 d) k in
  d_set_ll4 d (zset (d_ll4 d) k
    (if Z.land i 1 =? 0 then Z.lor (Z.land old 240) n
     else Z.land (Z.lor (Z.land old 15) (Z.shiftl n 4)) 255)).
Definition set_ll (d : dst) (i n : Z) : dst :=
  set_ll4 (d_set_ll16 d (zset (d_ll16 d) i (Z.land n 65535))) i (Z.shiftr n 16).

(* [comment removed for export] *)
Fixpoint iif_loop (fuel : nat) (cftab : zarr) (indx nb na : Z) : Z :=
  match fuel with
  | O => nb
  | S f => let mid := Z.shiftr (nb + na) 1 in
           let '(nb', na') := if zget cftab mid <=? indx then (mid, na) else (nb, mid) in
           if na' - nb' =? 1 then nb' else iif_loop f cftab indx nb' na'
  end.
Definition indexIntoF (indx : Z) (cftab : zarr) : Z := iif_loop 9 cftab indx 0 256.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive dres : Type :=
| DGo (lbl : Z) (L : dsv) (d : dst) (s : dstrm)          (* [comment removed for export] *)
| DRet (rv : Z) (L : dsv) (d : dst) (s : dstrm)          (* [comment removed for export] *)
| DRetNoSave (rv : Z) (L : dsv) (d : dst) (s : dstrm).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint mkmaps (n : nat) (i : Z) (inUse s2u : zarr) (nInUse : Z) : zarr * Z :=
  match n with
  | O => (s2u, nInUse)
  | S n' => if negb (zget inUse i =? 0)
            then mkmaps n' (i + 1) inUse (zset s2u nInUse i) (nInUse + 1)
            else mkmaps n' (i + 1) inUse s2u nInUse
  end.
Definition makeMaps_d (d : dst) : dst :=
  let '(s2u, n) := mkmaps 256 0 (d_inUse d) (d_s2u d) 0 in d_set_nInUse (d_set_s2u d s2u) n.

(* [comment removed for export] *)
Fixpoint clear256 (n : nat) (i : Z) (a : zarr) : zarr :=
  match n with O => a | S n' => clear256 n' (i + 1) (zset a i 0) end.

(* [comment removed for export] *)
Fixpoint pos_init (n : nat) (v : Z) (pos : zarr) : zarr :=
  match n with O => pos | S n' => pos_init n' (v + 1) (zset pos v v) end.
(* [comment removed for export] *)
Fixpoint pos_shift (n : nat) (v : Z) (pos : zarr) : zarr :=
  match n with
  | O => pos
  | S n' => if 0 <? v then pos_shift n' (v - 1) (zset pos v (zget pos (v - 1))) else pos
  end.
(* [comment removed for export] *)
Fixpoint sel_undo (n : nat) (i : Z) (pos selMtf sel : zarr) : zarr * zarr :=
  match n with
  | O => (pos, sel)
  | S n' => let v := zget selMtf i in
            let tmp := zget pos v in
            let pos1 := zset (pos_shift 8 v pos) 0 tmp in
            sel_undo n' (i + 1) pos1 selMtf (zset sel i tmp)
  end.

(* [comment removed for export] *)
Fixpoint minmax_len (n : nat) (i : Z) (len : zarr) (off minLen maxLen : Z) : Z * Z :=
  match n with
  | O => (minLen, maxLen)
  | S n' => let l := zget len (off + i) in
            let maxLen' := if maxLen <? l then l else maxLen in
            let minLen' := if l <? minLen then l else minLen in
            minmax_len n' (i + 1) len off minLen' maxLen'
  end.
(* [comment removed for export] *)
Fixpoint make_tables (n : nat) (t : Z) (alphaSize : Z) (d : dst) : dst :=
  match n with
  | O => d
  | S n' =>
      let off := 258 * t in
      let '(minLen, maxLen) := minmax_len (Z.to_nat alphaSize) 0 (d_len d) off 32 0 in
      let '(li, ba, pe) := hbCreateDecodeTables (d_limit d) (d_base d) (d_perm d) (d_len d) off minLen maxLen alphaSize in
      let d1 := d_set_minLens (d_set_perm (d_set_base (d_set_limit d li) ba) pe) (zset (d_minLens d) t minLen) in
      make_tables n' (t + 1) alphaSize d1
  end.

(* [comment removed for export] *)
Fixpoint mtfinit_j (n : nat) (jj ii kk : Z) (mtfa : zarr) : zarr * Z :=
  match n with
  | O => (mtfa, kk)
  | S n' => mtfinit_j n' (jj - 1) ii (kk - 1) (zset mtfa kk (ii * 16 + jj))
  end.
Fixpoint mtfinit_i (n : nat) (ii kk : Z) (mtfa mtfbase : zarr) : zarr * zarr :=
  match n with
  | O => (mtfa, mtfbase)
  | S n' => let '(mtfa', kk') := mtfinit_j 16 15 ii kk mtfa in
            mtfinit_i n' (ii - 1) kk' mtfa' (zset mtfbase ii (kk' + 1))
  end.
Definition mtf_init (d : dst) : dst :=
  let '(a, b) := mtfinit_i 16 15 4095 (d_mtfa d) (d_mtfbase d) in d_set_mtfbase (d_set_mtfa d a) b.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint mtf_sh4 (n : nat) (mtfa : zarr) (pp nn : Z) : zarr * Z :=
  match n with
  | O => (mtfa, nn)
  | S n' => if 3 <? nn then
              let z := pp + nn in
              let a1 := zset mtfa z (zget mtfa (z - 1)) in
              let a2 := zset a1 (z - 1) (zget a1 (z - 2)) in
              let a3 := zset a2 (z - 2) (zget a2 (z - 3)) in
              let a4 := zset a3 (z - 3) (zget a3 (z - 4)) in
              mtf_sh4 n' a4 pp (nn - 4)
            else (mtfa, nn)
  end.
(* [comment removed for export] *)
Fixpoint mtf_sh1 (n : nat) (mtfa : zarr) (pp nn : Z) : zarr :=
  match n with
  | O => mtfa
  | S n' => if 0 <? nn then mtf_sh1 n' (zset mtfa (pp + nn) (zget mtfa (pp + nn - 1))) pp (nn - 1) else mtfa
  end.
(* [comment removed for export] *)
Fixpoint mtf_shdown (n : nat) (mtfa : zarr) (pp b : Z) : zarr :=
  match n with
  | O => mtfa
  | S n' => if b <? pp then mtf_shdown n' (zset mtfa pp (zget mtfa (pp - 1))) (pp - 1) b else mtfa
  end.
(* [comment removed for export] *)
Fixpoint mtf_pull (n : nat) (mtfa mtfbase : zarr) (lno : Z) : zarr * zarr :=
  match n with
  | O => (mtfa, mtfbase)
  | S n' => if 0 <? lno then
              let b := zget mtfbase lno - 1 in
              let mtfbase1 := zset mtfbase lno b in
              let mtfa1 := zset mtfa b (zget mtfa (zget mtfbase1 (lno - 1) + 15)) in
              mtf_pull n' mtfa1 mtfbase1 (lno - 1)
            else (mtfa, mtfbase)
  end.
(* [comment removed for export] *)
Fixpoint mtfrb_j (n : nat) (jj ii kk : Z) (mtfa mtfbase : zarr) : zarr * Z :=
  match n with
  | O => (mtfa, kk)
  | S n' => mtfrb_j n' (jj - 1) ii (kk - 1) (zset mtfa kk (zget mtfa (zget mtfbase ii + jj))) mtfbase
  end.
Fixpoint mtfrb_i (n : nat) (ii kk : Z) (mtfa mtfbase : zarr) : zarr * zarr :=
  match n with
  | O => (mtfa, mtfbase)
  | S n' => let '(mtfa', kk') := mtfrb_j 16 15 ii kk mtfa mtfbase in
            mtfrb_i n' (ii - 1) kk' mtfa' (zset mtfbase ii (kk' + 1))
  end.

(* [comment removed for export] *)
Definition mtf_decode (d : dst) (nn : Z) : Z * dst :=
  let mtfa := d_mtfa d in let mtfbase := d_mtfbase d in
  if nn <? 16 then
    let pp := zget mtfbase 0 in
    let uc := zget mtfa (pp + nn) in
    let '(a1, nn1) := mtf_sh4 4 mtfa pp nn in
    let a2 := mtf_sh1 4 a1 pp nn1 in
    (uc, d_set_mtfa d (zset a2 pp uc))
  else
    let lno := nn / 16 in let off := nn mod 16 in
    let pp := zget mtfbase lno + off in
    let uc := zget mtfa pp in
    let a1 := mtf_shdown 16 mtfa pp (zget mtfbase lno) in
    let mtfbase1 := zset mtfbase lno (zget mtfbase lno + 1) in
    let '(a2, mtfbase2) := mtf_pull 16 a1 mtfbase1 lno in
    let b0 := zget mtfbase2 0 - 1 in
    let mtfbase3 := zset mtfbase2 0 b0 in
    let a3 := zset a2 b0 uc in
    let '(a4, mtfbase4) := if b0 =? 0 then mtfrb_i 16 15 4095 a3 mtfbase3 else (a3, mtfbase3) in
    (uc, d_set_mtfbase (d_set_mtfa d a4) mtfbase4).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint unz_check (n : nat) (i : Z) (unz : zarr) (nblock : Z) : Z :=
  match n with
  | O => i
  | S n' => let u := zget unz i in
            if (u <? 0) || (nblock <? u) then i else unz_check n' (i + 1) unz nblock
  end.
(* [comment removed for export] *)
Fixpoint cf_copy (n : nat) (i : Z) (unz cf : zarr) : zarr :=
  match n with O => cf | S n' => cf_copy n' (i + 1) unz (zset cf i (zget unz (i - 1))) end.
Fixpoint cf_accum (n : nat) (i : Z) (cf : zarr) : zarr :=
  match n with O => cf | S n' => cf_accum n' (i + 1) (zset cf i (zget cf i + zget cf (i - 1))) end.
(* [comment removed for export] *)
Fixpoint cf_check1 (n : nat) (i : Z) (cf : zarr) (nblock : Z) : Z :=
  match n with
  | O => i
  | S n' => let c := zget cf i in if (c <? 0) || (nblock <? c) then i else cf_check1 n' (i + 1) cf nblock
  end.
(* [comment removed for export] *)
Fixpoint cf_check2 (n : nat) (i : Z) (cf : zarr) : Z :=
  match n with
  | O => i
  | S n' => if zget cf i <? zget cf (i - 1) then i else cf_check2 n' (i + 1) cf
  end.
(* [comment removed for export] *)
Fixpoint cf_dup (n : nat) (i : Z) (cf cfc : zarr) : zarr :=
  match n with O => cfc | S n' => cf_dup n' (i + 1) cf (zset cfc i (zget cf i)) end.

(* [comment removed for export] *)
Fixpoint tinv_fast (n : nat) (i : Z) (tt cf : zarr) : zarr * zarr :=
  match n with
  | O => (tt, cf)
  | S n' => let uc := Z.land (zget tt i) 255 in
            let k := zget cf uc in
            tinv_fast n' (i + 1) (zset tt k (Z.lor (zget tt k) (Z.shiftl i 8))) (zset cf uc (k + 1))
  end.
(* [comment removed for export] *)
Fixpoint tvec_small (n : nat) (i : Z) (d : dst) : dst :=
  match n with
  | O => d
  | S n' => let uc := Z.land (zget (d_ll16 d) i) 255 in
            let k := zget (d_cftabCopy d) uc in
            let d1 := set_ll d i k in
            tvec_small n' (i + 1) (d_set_cftabCopy d1 (zset (d_cftabCopy d1) uc (k + 1)))
  end.
(* [comment removed for export] *)
Fixpoint prev_loop (n : nat) (i j : Z) (d : dst) : Z * Z * dst :=
  match n with
  | O => (i, j, d)
  | S n' => let tmp := get_ll d j in
            let d1 := set_ll d j i in
            if j =? d_origPtr d then (j, tmp, d1) else prev_loop n' j tmp d1
  end.

(* [comment removed for export] *)
Fixpoint run_write (n : nat) (small : bool) (uc nblock es nbMAX : Z) (d : dst) : Z * Z * dst * bool :=
  match n with
  | O => (nblock, es, d, false)
  | S n' =>
      if 0 <? es then
        if nbMAX <=? nblock then (nblock, es, d, true)
        else let d1 := if small then d_set_ll16 d (zset (d_ll16 d) nblock uc)
                       else d_set_tt d (zset (d_tt d) nblock uc) in
             run_write n' small uc (nblock + 1) (es - 1) nbMAX d1
      else (nblock, es, d, false)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition smallb (d : dst) : bool := negb (d_small d =? 0).

(* [comment removed for export] *)
Definition mtf_val_start (lbl1 : Z) (L : dsv) (d : dst) (s : dstrm) : dres :=
  if sv_groupPos L =? 0 then
    let gNo := sv_groupNo L + 1 in
    if sv_nSelectors L <=? gNo then DRet BZ_DATA_ERROR (sv_set_groupNo L gNo) d s
    else
      let gSel := zget (d_sel d) gNo in
      let gMinlen := zget (d_minLens d) gSel in
      let L1 := sv_set_gPtr (sv_set_gMinlen (sv_set_gSel (sv_set_groupPos (sv_set_groupNo L gNo) (BZ_G_SIZE - 1)) gSel) gMinlen) true in
      DGo lbl1 (sv_set_zn L1 gMinlen) d s
  else
    let L1 := sv_set_groupPos L (sv_groupPos L - 1) in
    DGo lbl1 (sv_set_zn L1 (sv_gMinlen L1)) d s.

(* [comment removed for export] *)
Definition BZ_X_MTF_1 : Z := 36.
Definition BZ_X_MTF_3 : Z := 38.
Definition BZ_X_MTF_5 : Z := 40.

(* [comment removed for export] *)
Definition run_body (L : dsv) (d : dst) (s : dstrm) : dres :=
  if 2097152 <=? sv_N L then DRet BZ_DATA_ERROR L d s
  else
    let es := if sv_nextSym L =? BZ_RUNA then sv_es L + sv_N L
              else if sv_nextSym L =? BZ_RUNB then sv_es L + 2 * sv_N L else sv_es L in
    mtf_val_start BZ_X_MTF_3 (sv_set_N (sv_set_es L es) (2 * sv_N L)) d s.

(* [comment removed for export] *)
Definition block_end (L : dsv) (d : dst) (s : dstrm) : dres :=
  let nblock := sv_nblock L in
  if (d_origPtr d <? 0) || (nblock <=? d_origPtr d) then DRet BZ_DATA_ERROR L d s else
  let i1 := unz_check 256 0 (d_unzftab d) nblock in
  if i1 <? 256 then DRet BZ_DATA_ERROR (sv_set_i L i1) d s else
  let cf0 := zset (d_cftab d) 0 0 in
  let cf1 := cf_copy 256 1 (d_unzftab d) cf0 in
  let cf2 := cf_accum 256 1 cf1 in
  let d1 := d_set_cftab d cf2 in
  let i2 := cf_check1 257 0 cf2 nblock in
  if i2 <? 257 then DRet BZ_DATA_ERROR (sv_set_i L i2) d1 s else
  let i3 := cf_check2 256 1 cf2 in
  if i3 <? 257 then DRet BZ_DATA_ERROR (sv_set_i L i3) d1 s else
  let d2 := d_set_state (d_set_cbcrc (d_set_out_ch (d_set_out_len d1 0) 0) crc_init) BZ_X_OUTPUT in
  let cap := 100000 * d_bs100k d2 in
  if smallb d2 then
    let d3 := d_set_cftabCopy d2 (cf_dup 257 0 (d_cftab d2) (d_cftabCopy d2)) in
    let d4 := tvec_small (Z.to_nat nblock) 0 d3 in
    let i0 := d_origPtr d4 in
    let j0 := get_ll d4 i0 in
    let '(i5, j5, d5) := prev_loop (S (Z.to_nat nblock)) i0 j0 d4 in
    let L5 := sv_set_j (sv_set_i L i5) j5 in
    let d6 := d_set_nused (d_set_tPos d5 (d_origPtr d5)) 0 in
    let d7 := if d_rand d6 =? 0 then d6 else d_set_rTPos (d_set_rNToGo d6 0) 0 in
    if cap <=? d_tPos d7 then DRetNoSave 1 L5 d7 s else
    let k0 := indexIntoF (d_tPos d7) (d_cftab d7) in
    let d8 := d_set_nused (d_set_tPos (d_set_k0 d7 k0) (get_ll d7 (d_tPos d7))) 1 in
    let d9 := if d_rand d8 =? 0 then d8
              else let d' := rand_upd d8 in d_set_k0 d' (Z.lxor (d_k0 d') (rand_mask d')) in
    DRet BZ_OK L5 d9 s
  else
    let '(tt1, cf3) := tinv_fast (Z.to_nat nblock) 0 (d_tt d2) (d_cftab d2) in
    let d3 := d_set_cftab (d_set_tt d2 tt1) cf3 in
    let L3 := sv_set_i L nblock in
    let d4 := d_set_nused (d_set_tPos d3 (Z.shiftr (zget tt1 (d_origPtr d3)) 8)) 0 in
    let d5 := if d_rand d4 =? 0 then d4 else d_set_rTPos (d_set_rNToGo d4 0) 0 in
    if cap <=? d_tPos d5 then DRetNoSave 1 L3 d5 s else
    let w := zget tt1 (d_tPos d5) in
    let d6 := d_set_nused (d_set_tPos (d_set_k0 d5 (Z.land w 255)) (Z.shiftr w 8)) 1 in
    let d7 := if d_rand d6 =? 0 then d6
              else let d' := rand_upd d6 in d_set_k0 d' (Z.lxor (d_k0 d') (rand_mask d')) in
    DRet BZ_OK L3 d7 s.

(* [comment removed for export] *)
Definition sym_dispatch (L : dsv) (d : dst) (s : dstrm) : dres :=
  let ns := sv_nextSym L in
  if ns =? sv_EOB L then block_end L d s
  else if (ns =? BZ_RUNA) || (ns =? BZ_RUNB) then run_body (sv_set_N (sv_set_es L (-1)) 1) d s
  else if sv_nblockMAX L <=? sv_nblock L then DRet BZ_DATA_ERROR L d s
  else
    let '(uc, d1) := mtf_decode d (ns - 1) in
    let u := zget (d_s2u d1) uc in
    let d2 := d_set_unzftab d1 (zincr (d_unzftab d1) u) in
    let nb := sv_nblock L in
    let d3 := if smallb d2 then d_set_ll16 d2 (zset (d_ll16 d2) nb u) else d_set_tt d2 (zset (d_tt d2) nb u) in
    mtf_val_start BZ_X_MTF_5 (sv_set_nblock L (nb + 1)) d3 s.

(* [comment removed for export] *)
Definition run_exit (L : dsv) (d : dst) (s : dstrm) : dres :=
  let es := sv_es L + 1 in
  let uc := zget (d_s2u d) (zget (d_mtfa d) (zget (d_mtfbase d) 0)) in
  let d1 := d_set_unzftab d (zset (d_unzftab d) uc (zget (d_unzftab d) uc + es)) in
  let '(nb, es', d2, failed) := run_write (Z.to_nat es) (smallb d1) uc (sv_nblock L) es (sv_nblockMAX L) d1 in
  let L2 := sv_set_es (sv_set_nblock L nb) es' in
  if failed then DRet BZ_DATA_ERROR L2 d2 s else sym_dispatch L2 d2 s.

(* [comment removed for export] *)
Definition mtf_val_loop (which : Z) (L : dsv) (d : dst) (s : dstrm) : dres :=
  let zn := sv_zn L in let zvec := sv_zvec L in let g := 258 * sv_gSel L in
  if 20 <? zn then DRet BZ_DATA_ERROR L d s
  else if zvec <=? zget (d_limit d) (g + zn) then
    let k := zvec - zget (d_base d) (g + zn) in
    if (k <? 0) || (BZ_MAX_ALPHA_SIZE <=? k) then DRet BZ_DATA_ERROR L d s
    else
      let lval := zget (d_perm d) (g + k) in
      let L1 := sv_set_nextSym L lval in
      if which =? 3 then
        (if (lval =? BZ_RUNA) || (lval =? BZ_RUNB) then run_body L1 d s else run_exit L1 d s)
      else sym_dispatch L1 d s
  else DGo (which + 36) (sv_set_zn L (zn + 1)) d s.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint map2_outer (n : nat) (i : Z) (L : dsv) (d : dst) (s : dstrm) : dres :=
  match n with
  | O => DRet BZ_DATA_ERROR L d s   (* [comment removed for export] *)
  | S n' =>
      if 16 <=? i then
        (* [comment removed for export] *)
        let d1 := makeMaps_d d in
        let L1 := sv_set_i L i in
        if d_nInUse d1 =? 0 then DRet BZ_DATA_ERROR L1 d1 s
        else DGo 30 (sv_set_alphaSize L1 (d_nInUse d1 + 2)) d1 s
      else if negb (zget (d_inUse16 d) i =? 0) then DGo 29 (sv_set_j (sv_set_i L i) 0) d s
      else map2_outer n' (i + 1) L d s
  end.

(* [comment removed for export] *)
Definition coding_check (L : dsv) (d : dst) (s : dstrm) : dres :=
  if (sv_curr L <? 1) || (20 <? sv_curr L) then DRet BZ_DATA_ERROR L d s else DGo 34 L d s.

(* [comment removed for export] *)
Definition after_tables (L : dsv) (d : dst) (s : dstrm) : dres :=
  let nG := sv_nGroups L in
  let d1 := make_tables (Z.to_nat nG) 0 (sv_alphaSize L) d in
  let L1 := sv_set_groupPos (sv_set_groupNo (sv_set_nblockMAX (sv_set_EOB (sv_set_t (sv_set_i L (sv_alphaSize L)) nG)
              (d_nInUse d1 + 1)) (100000 * d_bs100k d1)) (-1)) 0 in
  let d2 := d_set_unzftab d1 (clear256 256 0 (d_unzftab d1)) in
  let d3 := mtf_init d2 in
  mtf_val_start BZ_X_MTF_1 (sv_set_nblock (sv_set_i L1 256) 0) d3 s.

Definition u32 (x : Z) : Z := x mod 4294967296.

(* [comment removed for export] *)
Definition gb_after (lbl v : Z) (L : dsv) (d : dst) (s : dstrm) : dres :=
  match Z.to_nat (lbl - 10) with
  | 0%nat => if v =? 66 then DGo 11 L d s else DRet BZ_DATA_ERROR_MAGIC L d s          (* [comment removed for export] *)
  | 1%nat => if v =? 90 then DGo 12 L d s else DRet BZ_DATA_ERROR_MAGIC L d s          (* [comment removed for export] *)
  | 2%nat => if v =? 104 then DGo 13 L d s else DRet BZ_DATA_ERROR_MAGIC L d s         (* [comment removed for export] *)
  | 3%nat => (* [comment removed for export] *)
      let d1 := d_set_bs100k d v in
      if (v <? 49) || (57 <? v) then DRet BZ_DATA_ERROR_MAGIC L d1 s
      else let d2 := d_set_bs100k d1 (v - 48) in
           let d3 := if smallb d2 then d_set_ll_al d2 true else d_set_tt_al d2 true in
           DGo 14 L d3 s
  | 4%nat => if v =? 23 then DGo 42 L d s else if v =? 49 then DGo 15 L d s else DRet BZ_DATA_ERROR L d s
  | 5%nat => if v =? 65 then DGo 16 L d s else DRet BZ_DATA_ERROR L d s
  | 6%nat => if v =? 89 then DGo 17 L d s else DRet BZ_DATA_ERROR L d s
  | 7%nat => if v =? 38 then DGo 18 L d s else DRet BZ_DATA_ERROR L d s
  | 8%nat => if v =? 83 then DGo 19 L d s else DRet BZ_DATA_ERROR L d s
  | 9%nat => if v =? 89 then DGo 20 L (d_set_sbcrc (d_set_blockNo d (d_blockNo d + 1)) 0) s else DRet BZ_DATA_ERROR L d s
  | 10%nat => DGo 21 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s
  | 11%nat => DGo 22 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s
  | 12%nat => DGo 23 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s
  | 13%nat => DGo 24 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s
  | 14%nat => DGo 25 L (d_set_origPtr (d_set_rand d v) 0) s
  | 15%nat => DGo 26 L (d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v)) s
  | 16%nat => DGo 27 L (d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v)) s
  | 17%nat =>
      let d1 := d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v) in
      if d_origPtr d1 <? 0 then DRet BZ_DATA_ERROR L d1 s
      else if 10 + 100000 * d_bs100k d1 <? d_origPtr d1 then DRet BZ_DATA_ERROR L d1 s
      else DGo 28 (sv_set_i L 0) d1 s
  | 18%nat => (* [comment removed for export] *)
      let d1 := d_set_inUse16 d (zset (d_inUse16 d) (sv_i L) (if v =? 1 then 1 else 0)) in
      let i1 := sv_i L + 1 in
      if i1 <? 16 then DGo 28 (sv_set_i L i1) d1 s
      else let d2 := d_set_inUse d1 (clear256 256 0 (d_inUse d1)) in
           map2_outer 17 0 (sv_set_i L 256) d2 s
  | 19%nat => (* [comment removed for export] *)
      let d1 := if v =? 1 then d_set_inUse d (zset (d_inUse d) (sv_i L * 16 + sv_j L) 1) else d in
      let j1 := sv_j L + 1 in
      if j1 <? 16 then DGo 29 (sv_set_j L j1) d1 s
      else map2_outer 17 (sv_i L + 1) (sv_set_j L j1) d1 s
  | 20%nat => if (v <? 2) || (BZ_N_GROUPS <? v) then DRet BZ_DATA_ERROR (sv_set_nGroups L v) d s
             else DGo 31 (sv_set_nGroups L v) d s
  | 21%nat => if v <? 1 then DRet BZ_DATA_ERROR (sv_set_nSelectors L v) d s
             else DGo 32 (sv_set_j (sv_set_i (sv_set_nSelectors L v) 0) 0) d s
  | 22%nat => (* [comment removed for export] *)
      if v =? 0 then
        let i := sv_i L in let j := sv_j L in
        let d1 := if i <? BZ_MAX_SELECTORS then d_set_selMtf d (zset (d_selMtf d) i j) else d in
        let i1 := i + 1 in
        if i1 <? sv_nSelectors L then DGo 32 (sv_set_j (sv_set_i L i1) 0) d1 s
        else
          (* [comment removed for export] *)
          let nSel := if BZ_MAX_SELECTORS <? sv_nSelectors L then BZ_MAX_SELECTORS else sv_nSelectors L in
          let pos0 := pos_init (Z.to_nat (sv_nGroups L)) 0 znew in
          let '(_, sel1) := sel_undo (Z.to_nat nSel) 0 pos0 (d_selMtf d1) (d_sel d1) in
          DGo 33 (sv_set_t (sv_set_i (sv_set_nSelectors L nSel) nSel) 0) (d_set_sel d1 sel1) s
      else
        let j1 := sv_j L + 1 in
        if sv_nGroups L <=? j1 then DRet BZ_DATA_ERROR (sv_set_j L j1) d s
        else DGo 32 (sv_set_j L j1) d s
  | 23%nat => (* [comment removed for export] *)
      coding_check (sv_set_i (sv_set_curr L v) 0) d s
  | 24%nat => (* [comment removed for export] *)
      if v =? 0 then
        let t := sv_t L in let i := sv_i L in
        let d1 := d_set_len d (zset (d_len d) (258 * t + i) (sv_curr L)) in
        let i1 := i + 1 in
        if i1 <? sv_alphaSize L then coding_check (sv_set_i L i1) d1 s
        else let t1 := t + 1 in
             if t1 <? sv_nGroups L then DGo 33 (sv_set_t (sv_set_i L i1) t1) d1 s
             else after_tables (sv_set_t (sv_set_i L i1) t1) d1 s
      else DGo 35 L d s
  | 25%nat => coding_check (sv_set_curr L (if v =? 0 then sv_curr L + 1 else sv_curr L - 1)) d s
  | 26%nat => mtf_val_loop 1 (sv_set_zvec L v) d s
  | 27%nat => mtf_val_loop 1 (sv_set_zvec (sv_set_zj L v) (Z.lor (Z.shiftl (sv_zvec L) 1) v)) d s
  | 28%nat => mtf_val_loop 3 (sv_set_zvec L v) d s
  | 29%nat => mtf_val_loop 3 (sv_set_zvec (sv_set_zj L v) (Z.lor (Z.shiftl (sv_zvec L) 1) v)) d s
  | 30%nat => mtf_val_loop 5 (sv_set_zvec L v) d s
  | 31%nat => mtf_val_loop 5 (sv_set_zvec (sv_set_zj L v) (Z.lor (Z.shiftl (sv_zvec L) 1) v)) d s
  | 32%nat => if v =? 114 then DGo 43 L d s else DRet BZ_DATA_ERROR L d s
  | 33%nat => if v =? 69 then DGo 44 L d s else DRet BZ_DATA_ERROR L d s
  | 34%nat => if v =? 56 then DGo 45 L d s else DRet BZ_DATA_ERROR L d s
  | 35%nat => if v =? 80 then DGo 46 L d s else DRet BZ_DATA_ERROR L d s
  | 36%nat => if v =? 144 then DGo 47 L (d_set_sccrc d 0) s else DRet BZ_DATA_ERROR L d s
  | 37%nat => DGo 48 L (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) s
  | 38%nat => DGo 49 L (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) s
  | 39%nat => DGo 50 L (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) s
  | 40%nat => DRet BZ_STREAM_END L (d_set_state (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) BZ_X_IDLE) s
  | _ => DRet BZ_DATA_ERROR L d s   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition gb_bits (lbl : Z) (L : dsv) : Z :=
  match Z.to_nat (lbl - 10) with
  | 14%nat | 18%nat | 19%nat | 22%nat | 24%nat | 25%nat | 27%nat | 29%nat | 31%nat => 1
  | 20%nat => 3 | 21%nat => 15 | 23%nat => 5
  | 26%nat | 28%nat | 30%nat => sv_zn L
  | _ => 8
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint drun (fuel : nat) (lbl : Z) (L : dsv) (d : dst) (s : dstrm) : dres :=
  match fuel with
  | O => DRet BZ_OK L d s   (* [comment removed for export] *)
  | S f =>
      let d0 := d_set_state d lbl in
      let n := gb_bits lbl L in
      if n <=? d_bsLive d0 then
        let v := Z.land (Z.shiftr (d_bsBuff d0) (d_bsLive d0 - n)) (Z.shiftl 1 n - 1) in
        let d1 := d_set_bsLive d0 (d_bsLive d0 - n) in
        match gb_after lbl v L d1 s with
        | DGo lbl' L' d' s' => drun f lbl' L' d' s'
        | r => r
        end
      else
        match s_in s with
        | [] => DRet BZ_OK L d0 s
        | b :: rest =>
            let d1 := d_set_bsLive (d_set_bsBuff d0 (u32 (Z.lor (Z.shiftl (d_bsBuff d0) 8) b))) (d_bsLive d0 + 8) in
            drun f lbl L d1 (s_set_tin (s_set_in s rest) (s_tin s + 1))
        end
  end.

(* [comment removed for export] *)
Definition decompress (d : dst) (s : dstrm) : Z * dst * dstrm :=
  let d0 := if d_state d =? BZ_X_MAGIC_1 then d_set_sv d dsv_zero else d in
  let L := d_sv d0 in
  let fuel := (9 * length (s_in s) + 64)%nat in   (* [comment removed for export] *)
  match drun fuel (d_state d0) L d0 s with
  | DGo _ L' d' s' => (BZ_OK, d_set_sv d' L', s')          (* [comment removed for export] *)
  | DRet rv L' d' s' => (rv, d_set_sv d' L', s')
  | DRetNoSave rv _ d' s' => (rv, d', s')
  end.
