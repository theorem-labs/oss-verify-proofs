(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF SReach AllocSpec.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Notation wz := (Z_to_bv 64) (only parsing).
Notation errno_addr tp := (bv_unsigned tp + (-164))%Z (only parsing).
Definition zlength {X} (l : list X) : Z := Z.of_nat (length l).

Record http_addrs := mkHA {

  ha_LLVMFuzzerTestOneInput : Z; ha_httpmsg_compare : Z; ha_httpheader_free : Z; ha_httpmsg_destroy : Z;
  ha_vfmatch : Z; ha_parser_parse_responseline : Z; ha_match : Z; ha_parser_parse_headers : Z;
  ha_scanner_get_token : Z; ha_parser_get_entity_read_method : Z;
  ha_raw_find_str : Z;
  ha_parser_parse_entity : Z; ha_parser_request_init : Z; ha_parser_response_init : Z;
  ha_parser_parse : Z; ha_parser_append : Z;
  ha_ListInit : Z; ha_ListAddTail : Z; ha_ListDestroy : Z; ha_ListHead : Z; ha_ListNext : Z; ha_ListFind : Z;
  ha_FreeListInit : Z; ha_FreeListAlloc : Z; ha_FreeListFree : Z; ha_FreeListDestroy : Z;
  ha_str_alloc : Z; ha_memptr_cmp : Z; ha_memptr_cmp_nocase : Z;
  ha_membuffer_init : Z; ha_membuffer_destroy : Z; ha_membuffer_assign : Z; ha_membuffer_append : Z;
  ha_membuffer_insert : Z; ha_membuffer_append_str : Z; ha_membuffer_delete : Z;
  ha_parse_uri : Z; ha_parse_uric : Z; ha_UpnpPrintf : Z; ha_map_str_to_int : Z;

  ha_isalnum : Z; ha_isxdigit : Z; ha_tolower : Z; ha_errno_location : Z; ha_free : Z; ha_malloc : Z;
  ha_realloc : Z; ha_htons : Z; ha_inet_pton : Z; ha_sscanf : Z; ha_strtoll : Z; ha_strtol : Z; ha_atoi : Z;
  ha_memchr : Z; ha_memcpy : Z; ha_memmove : Z; ha_memset : Z; ha_strlen : Z; ha_strncasecmp : Z;
  ha_strncmp : Z; ha_strncpy : Z; ha_strstr : Z;

  ha_hdr_names : Z;
  ha_method_tab : Z;
  ha_gIF_INDEX : Z;
  ha_gmax : Z;
  ha_zero : Z;
  ha_initwascalled : Z;
  ha_got_gif : Z;
  ha_got_gmax : Z;

  ha_data_lo : Z; ha_data_hi : Z
}.

Definition UA : http_addrs := mkHA
  0x13fbc 0x14038 0x14068 0x140b0 0x14118 0x14904 0x14c14 0x14c4c 0x14fbc 0x15360 0x155d4 0x15704 0x15a98 0x15b38
  0x15bec 0x1601c 0x16078 0x160ec 0x16178 0x1627c 0x162a4 0x162e0 0x1639c 0x163cc 0x1641c 0x1648c
  0x16508 0x16570 0x16600 0x16690 0x166b8 0x16708 0x1684c 0x16864 0x16a10 0x16a64 0x16ba4 0x170e4 0x17234 0x173d8
  0x17548 0x17564 0x17580 0x17b68 0x17fb0 0x180f0 0x1995c 0x19ff0 0x1a008 0x1b1d0 0x23dc4 0x23f2c 0x23d2c
  0x23fe4 0x240e0 0x244e4 0x24660 0x248ac 0x2493c 0x24a00 0x24a60 0x24bdc
  0x2b1a8 0x2b3b8 0x2b468 0x2b470 0x3b700 0x3b708 0x2a118 0x2a120
  0x2a0a0 0x5c3f0.

Definition PA : http_addrs := mkHA
  0x13f30 0x13f9c 0x13fb0 0x13fe4 0x1403c 0x146a4 0x148a4 0x148dc 0x14bc0 0x14e90 0 0x150c4 0x153f4 0x1548c
  0x15538 0x158c8 0x15914 0x1597c 0x159e8 0x15adc 0x15af8 0x15b24 0x15bd0 0x15bf8 0x15c28 0x15c80
  0x15cd8 0x15d34 0x15db0 0x15e2c 0x15e44 0x15e88 0x15fa4 0x15fac 0x16128 0x1616c 0x16260 0x166ac 0x167d0 0x16974
  0x16a54 0x16a70 0x16a8c 0x17074 0x174bc 0x175fc 0x18e68 0x194fc 0x19514 0x1a6dc 0x232d0 0x23438 0x23238
  0x234f0 0x235ec 0x239f0 0x23b6c 0x23db8 0x23e48 0x23f0c 0x23f6c 0x240e8
  0x2a6b0 0x2a8c0 0x2a970 0x2a978 0x3ac10 0x3ac18 0x29620 0x29628
  0x29000 0x5b900.

Definition PARSE_SUCCESS : Z := 0.  Definition PARSE_INCOMPLETE : Z := 1.  Definition PARSE_INCOMPLETE_ENTITY : Z := 2.
Definition PARSE_FAILURE : Z := 3.  Definition PARSE_OK : Z := 4.  Definition PARSE_NO_MATCH : Z := 5.  Definition PARSE_CONTINUE_1 : Z := 6.
Definition TT_IDENTIFIER : Z := 0. Definition TT_WHITESPACE : Z := 1. Definition TT_CRLF : Z := 2.
Definition TT_CTRL : Z := 3. Definition TT_SEPARATOR : Z := 4. Definition TT_QUOTEDSTRING : Z := 5.
Definition POS_REQUEST_LINE : Z := 0. Definition POS_RESPONSE_LINE : Z := 1. Definition POS_HEADERS : Z := 2.
Definition POS_ENTITY : Z := 3. Definition POS_COMPLETE : Z := 4.
Definition ENTREAD_DETERMINE_READ_METHOD : Z := 1. Definition ENTREAD_USING_CLEN : Z := 2. Definition ENTREAD_USING_CHUNKED : Z := 3.
Definition ENTREAD_UNTIL_CLOSE : Z := 4. Definition ENTREAD_CHUNKY_BODY : Z := 5. Definition ENTREAD_CHUNKY_HEADERS : Z := 6.
Definition UPNP_E_OUTOF_MEMORY : Z := -104. Definition UPNP_E_OUTOF_BOUNDS : Z := -506. Definition UPNP_E_INVALID_URL : Z := -108.
Definition HTTP_SUCCESS : Z := 1.
Definition MEMBUF_DEF_SIZE_INC : Z := 5.
Definition G_MAX_CONTENT_LENGTH : Z := 64000.
Definition FREELISTSIZE : Z := 100.
Definition NUM_HTTP_METHODS : Z := 11. Definition NUM_HTTP_HEADER_NAMES : Z := 33.

Definition MEMBUFFER_SIZEOF : Z := 32.
Definition MEMPTR_SIZEOF : Z := 16.
Definition SCANNER_SIZEOF : Z := 24.
Definition HEADER_SIZEOF : Z := 88.
Definition LISTNODE_SIZEOF : Z := 24.
Definition LINKEDLIST_SIZEOF : Z := 96.
Definition URI_SIZEOF : Z := 216.
Definition HTTPMSG_SIZEOF : Z := 440.
Definition PARSER_SIZEOF : Z := 504.
Definition STRINT_SIZEOF : Z := 16.

Definition O_initialized : Z := 0.      Definition O_method : Z := 4.
Definition O_uri : Z := 8.
Definition O_request_method : Z := 224. Definition O_status_code : Z := 228.
Definition O_status_msg : Z := 232.
Definition O_amount_discarded : Z := 264.
Definition O_is_request : Z := 272.     Definition O_major_version : Z := 276.  Definition O_minor_version : Z := 280.
Definition O_headers : Z := 288.
Definition O_entity : Z := 384.
Definition O_msg : Z := 400.
Definition O_url_buf : Z := 432.
Definition O_http_error_code : Z := 440. Definition O_valid_ssdp_notify_hack : Z := 444.
Definition O_position : Z := 448.       Definition O_ent_position : Z := 452.
Definition O_content_length : Z := 456.
Definition O_chunk_size : Z := 464.     Definition O_entity_start_position : Z := 472.
Definition O_scanner : Z := 480.

Definition is_space (c : Z) : bool := (c =? 32) || ((9 <=? c) && (c <=? 13)).
Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).

Fixpoint cstr (bs : list Z) : list Z :=
  match bs with [] => [] | c :: bs' => if c =? 0 then [] else c :: cstr bs' end.
Fixpoint drop_while (f : Z -> bool) (l : list Z) : list Z :=
  match l with [] => [] | c :: l' => if f c then drop_while f l' else l end.
Fixpoint take_while_len (f : Z -> bool) (l : list Z) : nat :=
  match l with [] => 0%nat | c :: l' => if f c then S (take_while_len f l') else 0%nat end.

Inductive sdir := SD | SW | SL (c : Z).
Fixpoint scan_count (fmt : list sdir) (inp : list Z) (acc : Z) : Z :=
  match fmt with
  | [] => acc
  | SW :: fmt' => scan_count fmt' (drop_while is_space inp) acc
  | SL c :: fmt' => match inp with c' :: inp' => if c' =? c then scan_count fmt' inp' acc else acc | [] => acc end
  | SD :: fmt' =>
      let i1 := drop_while is_space inp in
      let i2 := match i1 with c :: r => if (c =? 43) || (c =? 45) then r else i1 | [] => i1 end in
      let nd := take_while_len is_digit i2 in
      if Nat.eqb nd 0 then acc else scan_count fmt' (skipn nd i2) (acc + 1)
  end.
Definition FMT_VERSION : list sdir := [SD; SW; SL 46; SW; SD].
Definition FMT_STATUSLINE : list sdir := [SD; SW; SL 46; SW; SD; SW; SD].

Fixpoint skip_runs (k : nat) (l : list Z) : option nat :=
  match k with
  | O => Some 0%nat
  | S k' => let a := take_while_len (fun c => negb (is_digit c)) l in
            let l1 := skipn a l in
            match l1 with [] => None | _ =>
              let b := take_while_len is_digit l1 in
              match skip_runs k' (skipn b l1) with None => None | Some r => Some (a + b + r)%nat end end
  end.
Definition statusline_walk_ok : Prop :=
  forall line, scan_count FMT_STATUSLINE (cstr line) 0 = 3 ->
  exists n, skip_runs 3 (cstr line) = Some n /\ (n <= length (cstr line))%nat.

Section REP.
Context {HCEIL : HasCeiling}.
Variable segs : list Segment.
Variable HA : http_addrs.
Variable AI : alloc_if segs.

Definition hK : Type := ai_K segs AI.
Definition PState : Type := ai_PS segs AI.
Definition hblock : Type := block hK.
Definition hAL : alloc_layout := ai_L segs AI.
Notation RHEAPx := (RHEAP segs AI).
Notation SREACHx := (@SREACH _ segs AI).

Fixpoint in_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ in_ivs X' a end.

Definition pclient (LB : list hblock) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop :=
  ~ in_ivs X a /\ client_addr AI LB SP a.
Definition ppres (LB : list hblock) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> pclient LB SP X a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma ppres_refl : forall LB SP X m, ppres LB SP X m m.
Proof. intros LB SP X m a _ _; auto. Qed.
#[using="Type"] Lemma ppres_trans : forall LB SP X m1 m2 m3, ppres LB SP X m1 m2 -> ppres LB SP X m2 m3 -> ppres LB SP X m1 m3.
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence|auto].
Qed.

Definition src_ok (LB : list hblock) (SP : Z) (S n : Z) : Prop :=
  SP <= S \/ (exists b, In b LB /\ blk_addr b <= S /\ S + n <= blk_addr b + blk_size b)
  \/ (exists lo hi, al_client_static hAL lo hi /\ lo <= S /\ S + n <= hi)
  \/ (S + n <= ha_data_lo HA).

Definition block_ok (A n : Z) : Prop := block_range AI A n.

Definition strint_cells (e : Z * Z) : list cell := [C8 (wz (fst e)); C4 (wz (snd e)); C4 (wz 0)].
Fixpoint strint_table (es : list (Z * Z)) : list cell :=
  match es with [] => [] | e :: es' => strint_cells e ++ strint_table es' end.

Definition HDR_NAMES : list (Z * Z) :=
  [(0x10311,25);(0x104b7,27);(0x10511,26);(0x1049e,28);(0x10630,29);(0x10415,1);(0x10318,2);(0x103b6,30);
   (0x10466,31);(0x105fb,3);(0x1060a,32);(0x10477,33);(0x1059f,4);(0x1063e,5);(0x10357,6);(0x1045d,7);
   (0x103a3,34);(0x10442,11);(0x104c6,12);(0x10439,13);(0x1061b,14);(0x1061e,15);(0x10380,35);(0x10521,17);
   (0x105ac,16);(0x1032d,18);(0x106cc,19);(0x106bb,20);(0x10643,36);(0x10539,21);(0x104ca,22);(0x103c7,24);
   (0x10485,23)].
Definition METHOD_TAB : list (Z * Z) :=
  [(0x106d7,1);(0x106be,2);(0x104dc,3);(0x103ac,5);(0x10489,9);(0x104ae,8);(0x10582,4);(0x106c2,6);(0x10492,7);
   (0x10582,11);(0x103da,0)].

Definition GD (m : mem) : Prop :=
  rw_cells segs m (ha_hdr_names HA) (strint_table HDR_NAMES)
  /\ rw_cells segs m (ha_method_tab HA) (strint_table METHOD_TAB)
  /\ rw_cells segs m (ha_gIF_INDEX HA) [C4 (wz 0xFFFFFFFF)]
  /\ rw_cells segs m (ha_gmax HA) [C8 (wz G_MAX_CONTENT_LENGTH)]
  /\ rw_cells segs m (ha_zero HA) [C1 (Z_to_bv 8 0)]
  /\ rw_cells segs m (ha_initwascalled HA) [C1 (Z_to_bv 8 0)]
  /\ rw_cells segs m (ha_got_gif HA) [C8 (wz (ha_gIF_INDEX HA))]
  /\ rw_cells segs m (ha_got_gmax HA) [C8 (wz (ha_gmax HA))].

Definition mbuf_cells (bufA len cap : Z) : list cell :=
  [C8 (wz bufA); C8 (wz len); C8 (wz cap); C8 (wz MEMBUF_DEF_SIZE_INC)].

Definition mbuf_rep (m : mem) (MB : Z) (B : list hblock) (A len cap : Z) : Prop :=
  match B with
  | [] => A = 0 /\ len = 0 /\ cap = 0 /\ rw_cells segs m MB (mbuf_cells 0 0 0)
  | [b] => A = blk_addr b /\ blk_size b = cap + 1 /\ 0 <= len <= cap /\ block_ok A (cap + 1)
           /\ rw_cells segs m MB (mbuf_cells A len cap)
           /\ exists bs, rw_cells segs m A [CB (Z.to_nat (cap + 1)) bs] /\ nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0)
  | _ => False
  end.

Definition mbuf_rep_bytes (m : mem) (MB : Z) (B : list hblock) (A len cap : Z) (bs : list byte) : Prop :=
  match B with
  | [] => A = 0 /\ len = 0 /\ cap = 0 /\ bs = [] /\ rw_cells segs m MB (mbuf_cells 0 0 0)
  | [b] => A = blk_addr b /\ blk_size b = cap + 1 /\ 0 <= len <= cap /\ block_ok A (cap + 1)
           /\ rw_cells segs m MB (mbuf_cells A len cap)
           /\ rw_cells segs m A [CB (Z.to_nat (cap + 1)) bs] /\ nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0)
  | _ => False
  end.

#[using="Type"] Lemma mbuf_rep_of_bytes : forall m MB B A len cap bs, mbuf_rep_bytes m MB B A len cap bs -> mbuf_rep m MB B A len cap.
Proof.
  intros m MB [|b [|b' B]] A len cap bs H; cbn in *; try tauto.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7). repeat (split; [assumption|]). exists bs. auto.
Qed.

Definition memptr_cells (bufA len : Z) : list cell := [C8 (wz bufA); C8 (wz len)].

Definition subrange (off n len : Z) : Prop := 0 <= off /\ 0 <= n /\ off + n <= len.

Record hdr := mkHdr { h_addr : Z; h_id : Z; h_nameA : Z; h_nameLen : Z; h_nameCap : Z;
                      h_valA : Z; h_valLen : Z; h_valCap : Z }.
Definition hdr_rep (m : mem) (BS : list hblock) (h : hdr) : Prop :=
  exists hb nb vb (pad : word), BS = [hb; vb; nb] /\ hb = (blk_id hb, h_addr h, HEADER_SIZEOF) /\ block_ok (h_addr h) HEADER_SIZEOF
  /\ rw_cells segs m (h_addr h) (memptr_cells (h_nameA h) (h_nameLen h) ++ [C4 (wz (h_id h)); C4 pad])
  /\ mbuf_rep m (h_addr h + 24) [vb] (h_valA h) (h_valLen h) (h_valCap h) /\ 1 <= h_valLen h
  /\ mbuf_rep m (h_addr h + 56) [nb] (h_nameA h) (h_nameLen h) (h_nameCap h) /\ 1 <= h_nameLen h
  /\ - 2^31 <= h_id h < 2^31.

Definition node_cells (pv nx item : Z) : list cell := [C8 (wz pv); C8 (wz nx); C8 (wz item)].

Inductive dlseg (m : mem) : list hblock -> Z -> Z -> Z -> Z -> list Z -> Prop :=
| dl_nil : forall TAIL pv, dlseg m [] TAIL pv TAIL pv []
| dl_cons : forall N pv nx TAIL last it items nb NB,
    N <> TAIL -> N <> 0 -> nb = (blk_id nb, N, LISTNODE_SIZEOF) -> block_ok N LISTNODE_SIZEOF ->
    rw_cells segs m N (node_cells pv nx it) ->
    dlseg m NB nx N TAIL last items ->
    dlseg m (nb :: NB) N pv TAIL last (it :: items).

Inductive hdrs_rep (m : mem) : list hblock -> list hdr -> Prop :=
| hr_nil : hdrs_rep m [] []
| hr_cons : forall HB HBS h hs, hdr_rep m HB h -> hdrs_rep m HBS hs -> hdrs_rep m (HB ++ HBS) (h :: hs).

Inductive flseg (m : mem) : list hblock -> Z -> nat -> Prop :=
| fl_nil : flseg m [] 0 0
| fl_cons : forall N nx (j1 j2 : word) nb FB k,
    N <> 0 -> nb = (blk_id nb, N, LISTNODE_SIZEOF) -> block_ok N LISTNODE_SIZEOF ->
    rw_cells segs m N [C8 (wz nx); C8 j1; C8 j2] -> flseg m FB nx k -> flseg m (nb :: FB) N (S k).

Definition llist_cells (first last size flh fk ffree fcmp : Z) : list cell :=
  [C8 (wz 0); C8 (wz first); C8 (wz 0);
   C8 (wz last); C8 (wz 0); C8 (wz 0);
   C8 (wz size);
   C8 (wz flh); C8 (wz LISTNODE_SIZEOF); C4 (wz FREELISTSIZE); C4 (wz fk);
   C8 (wz ffree); C8 (wz fcmp)].

Definition hlist_rep (m : mem) (L : Z) (NB HBS : list hblock) (hs : list hdr) (FB : list hblock) (fk : nat) : Prop :=
  exists first last flh,
    rw_cells segs m L (llist_cells first last (zlength hs) flh (Z.of_nat fk) (ha_httpheader_free HA) (ha_httpmsg_compare HA))
    /\ dlseg m NB first L (L + 24) last (map h_addr hs)
    /\ hdrs_rep m HBS hs
    /\ flseg m FB flh fk.

Record pst := mkPst {
  p_method : Z; p_request_method : Z; p_status_code : Z; p_is_request : Z; p_major : Z; p_minor : Z;
  p_smsgA : Z; p_smsgLen : Z; p_smsgCap : Z;
  p_amount_discarded : Z;
  p_hdrs : list hdr;
  p_entA : Z; p_entLen : Z;
  p_msgA : Z; p_msgLen : Z; p_msgCap : Z;
  p_url : Z;
  p_err : Z; p_hack : Z; p_position : Z; p_entpos : Z; p_clen : Z; p_chunk : Z; p_estart : Z;
  p_cursor : Z
}.

Definition parser_k1 (st : pst) : list cell := [C4 (wz 1); C4 (wz (p_method st))].
Definition parser_k3a (st : pst) : list cell :=
  [C4 (wz (p_request_method st)); C4 (wz (p_status_code st))].
Definition parser_k3b (st : pst) (pad : word) : list cell :=
  [C8 (wz 0); C4 (wz (p_is_request st)); C4 (wz (p_major st)); C4 (wz (p_minor st)); C4 pad].
Definition parser_k5c (P : Z) (st : pst) (pad1 pad2 : word) : list cell :=
  [C8 (wz (p_url st));
   C4 (wz (p_err st)); C4 (wz (p_hack st)); C4 (wz (p_position st)); C4 (wz (p_entpos st));
   C4 (wz (p_clen st)); C4 pad1; C8 (wz (p_chunk st)); C8 (wz (p_estart st));
   C8 (wz (P + O_msg)); C8 (wz (p_cursor st)); C4 (wz 0); C4 pad2].

Definition url_rep (m : mem) (UB : list hblock) (U : Z) : Prop :=
  match UB with
  | [] => U = 0
  | [b] => U = blk_addr b /\ U <> 0 /\ block_ok U (blk_size b) /\ 1 <= blk_size b
           /\ exists bs, rw_cells segs m U [CB (Z.to_nat (blk_size b)) bs]
              /\ nth_error bs (Z.to_nat (blk_size b - 1)) = Some (Z_to_bv 8 0)
  | _ => False
  end.

Definition pinv (st : pst) : Prop :=
  0 <= p_cursor st <= p_msgLen st /\ p_msgLen st <= p_msgCap st /\ p_msgCap st + 1 < 2^62
  /\ 0 <= p_estart st <= p_msgLen st
  /\ p_amount_discarded st = 0
  /\ 0 <= p_position st <= 4 /\ 1 <= p_entpos st <= 6
  /\ 0 <= p_clen st < 2^32 /\ 0 <= p_chunk st <= 2^31
  /\ 0 <= p_smsgLen st <= p_smsgCap st
  /\ - 2^31 <= p_method st < 2^31 /\ - 2^31 <= p_status_code st < 2^31
  /\ (0 <= p_is_request st <= 1).

Definition parser_rep (m : mem) (P : Z) (PB : list hblock) (st : pst) : Prop :=
  exists MB SB UB NB HBS (pad3 pad5a pad5b : word) (ujunk : list byte),
    PB = MB ++ SB ++ UB ++ NB ++ HBS
    /\ rw_cells segs m P (parser_k1 st)
    /\ rw_cells segs m (P + O_uri) [CB 216%nat ujunk]
    /\ rw_cells segs m (P + O_request_method) (parser_k3a st)
    /\ mbuf_rep m (P + O_status_msg) SB (p_smsgA st) (p_smsgLen st) (p_smsgCap st)
    /\ rw_cells segs m (P + O_amount_discarded) (parser_k3b st pad3)
    /\ hlist_rep m (P + O_headers) NB HBS (p_hdrs st) [] 0%nat
    /\ rw_cells segs m (P + O_entity) (memptr_cells (p_entA st) (p_entLen st))
    /\ mbuf_rep m (P + O_msg) MB (p_msgA st) (p_msgLen st) (p_msgCap st)
    /\ rw_cells segs m (P + O_url_buf) (parser_k5c P st pad5a pad5b)
    /\ url_rep m UB (p_url st)
    /\ pinv st.

Definition REGS := (word * word * word * word)%type.

Definition env_ok (m : mem) (sp tp : word) (lo : Z) (errv : word) (AB : Z) : Prop :=
  stk segs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ mem_inv segs m /\ GD m
  /\ tp = wz (al_tp hAL) /\ rw_cells segs m (al_errno hAL) [C4 errv]
  /\ RENV segs AI m AB /\ bv_unsigned sp <= AB
  /\ bv_unsigned sp + 1024 < 2^63.

Definition membuffer_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (MB : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(MB, MB + 32)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' MB (mbuf_cells 0 0 0).

Definition membuffer_init_stmt : Prop :=
  forall (MB : Z) (junk : list byte)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells segs m MB [CB 32%nat junk] -> MB mod 8 = 0 ->
  mem_inv segs m -> a0 = wz MB ->
  evt segs (membuffer_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MB m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_membuffer_init HA)) fc None m (seg_rom segs)).

Definition httpmsg_compare_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A B ia ib : Z) (ca cb : list cell),
  rw_cells segs m A (ca ++ [C4 (wz ia)]) -> cells_size ca = 16%nat -> A mod 8 = 0 ->
  rw_cells segs m B (cb ++ [C4 (wz ib)]) -> cells_size cb = 16%nat -> B mod 8 = 0 ->
  - 2^31 <= ia < 2^31 -> - 2^31 <= ib < 2^31 ->
  mem_inv segs m -> a0 = wz A -> a1 = wz B ->
  evt segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (if ia =? ib then 1 else 0)) a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom segs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_httpmsg_compare HA)) fc None m (seg_rom segs)).

Definition memptr_cmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' (bv_unsigned sp - 80) (bv_unsigned sp)
    /\ - 2^31 <= r < 2^31.

Definition memptr_cmp_stmt (nocase : bool) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (MP T n S : Z) (tok : list byte) (str slack tslack : list byte),
  rw_cells segs m MP (memptr_cells T n) -> MP mod 8 = 0 -> bv_unsigned sp <= MP   ->
  bytes_at segs m T (tok ++ tslack) -> zlength tok = n -> 1 <= n ->

  bytes_at segs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + zlength str + 1)) mod 8 <= zlength slack) ->
  stk segs m (bv_unsigned sp - 80) (bv_unsigned sp) -> mem_inv segs m ->
  a0 = wz MP -> a1 = wz S ->
  evt segs (fun ms' => exists r, memptr_cmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (if nocase then ha_memptr_cmp_nocase HA else ha_memptr_cmp HA)) fc None m (seg_rom segs)).

Definition map_str_to_int_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ne : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' (bv_unsigned sp - 144) (bv_unsigned sp)
    /\ (r = -1 \/ 0 <= r < ne).
Definition map_str_to_int_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (T n TAB ne cs : Z) (tok tslack : list byte) (es : list (Z * Z)),
  bytes_at segs m T (tok ++ tslack) -> zlength tok = n -> 1 <= n -> n < 2^62 ->
  rw_cells segs m TAB (strint_table es) -> zlength es = ne -> (ne = 11 \/ ne = 33) ->
  (TAB = ha_method_tab HA /\ es = METHOD_TAB \/ TAB = ha_hdr_names HA /\ es = HDR_NAMES) ->

  stk segs m (bv_unsigned sp - 144) (bv_unsigned sp) -> mem_inv segs m ->
  a0 = wz T -> a1 = wz n -> a2 = wz TAB -> a3 = wz ne -> a4 = wz cs -> (cs = 0 \/ cs = 1) ->
  evt segs (map_str_to_int_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ne m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_map_str_to_int HA)) fc None m (seg_rom segs)).

Inductive fmt_id := F_REQ09   | F_REQ
                  | F_RESP   | F_HDR   | F_CRLF   | F_CHUNK  .
Definition fmt_rodata (f : fmt_id) : Z :=
  match f with F_REQ09 => 0x10331 | F_REQ => 0x10423 | F_RESP => 0x10429
             | F_HDR => 0x102a7 | F_CRLF => 0x102ac | F_CHUNK => 0x1035b end.

Definition vfmatch_out_ok (f : fmt_id) (cur cur' len : Z) (outs : list (Z * Z)) (ival : Z) : Prop :=
  match f, outs with
  | F_REQ09, [(o1,l1);(o2,l2)] => subrange o1 l1 len /\ 1 <= l1 /\ o1 + l1 < len /\ subrange o2 l2 len /\ 1 <= l2 /\ o2 + l2 < cur'
  | F_REQ, [(o1,l1);(o2,l2);(o3,l3)] => subrange o1 l1 len /\ 1 <= l1 /\ o1 + l1 < len /\ subrange o2 l2 len /\ 1 <= l2
                                      /\ subrange o3 l3 len /\ o3 + l3 < cur'
  | F_RESP, [(o1,l1)] => subrange o1 l1 len /\ o1 + l1 < cur'
  | F_HDR, [(o1,l1)] => subrange o1 l1 len /\ o1 + l1 < cur'
  | F_CRLF, [] => True
  | F_CHUNK, [(o1,l1)] => subrange o1 l1 len /\ o1 + l1 < cur' /\ 0 <= ival < 2^31
  | _, _ => False
  end.

Definition aframe (m m' : mem) (LBX : list hblock) (sp tp : word) (lo : Z) (X : list (Z * Z)) (AB : Z) : Prop :=
  mem_inv segs m' /\ GD m' /\ stk segs m' lo (bv_unsigned sp) /\ RENV segs AI m' AB
  /\ (exists errv' : word, rw_cells segs m' (al_errno hAL) [C4 errv'])
  /\ ppres LBX (bv_unsigned sp) X m m'.

Definition str_alloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list hblock) (n lo AB : Z) (str : list byte) (m : mem) : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' LB sp tp lo [] AB
    /\ RHEAPx s' LB' m'
    /\ ( (a0 = wz 0 /\ LB' = LB)
       \/ (exists p U, a0 = wz U /\ U <> 0 /\ LB' = (p, U, n + 1) :: LB /\ block_ok U (n + 1)
             /\ rw_cells segs m' U [CB (Z.to_nat (n + 1)) (str ++ [Z_to_bv 8 0])]) ).
Definition str_alloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list hblock) (S n lo : Z) (str : list byte) (errv : word) (AB : Z),
  RHEAPx s LB m -> env_ok m sp tp lo errv AB -> lo <= bv_unsigned sp - (32 + 8192) ->
  bytes_at segs m S str -> zlength str = n -> 0 <= n < 2^32 - 1 ->
  src_ok LB (bv_unsigned sp) S n   ->
  a0 = wz S -> a1 = wz n ->
  SREACHx
    (str_alloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB n lo AB str m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_str_alloc HA)) fc None m (seg_rom segs))
    s LB.

Definition membuffer_assign_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LBX B : list hblock) (MB A len cap n lo AB : Z) (src : list byte) (m : mem) : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (B' : list hblock) (A' len' cap' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' LBX sp tp lo [(MB, MB + 32)] AB
    /\ RHEAPx s' LB' m' /\ Permutation LB' (B' ++ LBX)
    /\ mbuf_rep m' MB B' A' len' cap'
    /\ ( (r = 0 /\ len' = n /\ (n > 0 -> exists bs, mbuf_rep_bytes m' MB B' A' n cap' bs /\ firstn (Z.to_nat n) bs = src))
       \/ (r = UPNP_E_OUTOF_MEMORY /\ B' = B /\ A' = A /\ len' = len /\ cap' = cap) ).
Definition membuffer_assign_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX B : list hblock) (MB A len cap S n lo : Z)
         (src : list byte) (errv : word) (AB : Z),
  RHEAPx s (B ++ LBX) m -> env_ok m sp tp lo errv AB -> lo <= bv_unsigned sp - (48 + 8192) ->
  mbuf_rep m MB B A len cap -> MB mod 8 = 0 -> (bv_unsigned sp <= MB \/ in_block LBX MB) ->
  bytes_at segs m S src -> zlength src = n -> 0 <= n < 2^32 -> S <> 0 ->
  src_ok LBX (bv_unsigned sp) S n ->
  a0 = wz MB -> a1 = wz S -> a2 = wz n ->
  SREACHx
    (membuffer_assign_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX B MB A len cap n lo AB src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_membuffer_assign HA)) fc None m (seg_rom segs))
    s (B ++ LBX).

Definition membuffer_insert_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LBX B : list hblock) (MB A len cap n lo AB : Z) (old src : list byte) (m : mem) : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (B' : list hblock) (A' cap' : Z) (bs : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' LBX sp tp lo [(MB, MB + 32)] AB
    /\ RHEAPx s' LB' m' /\ Permutation LB' (B' ++ LBX)
    /\ ( (r = 0 /\ mbuf_rep_bytes m' MB B' A' (len + n) cap' bs /\ (n > 0 -> firstn (Z.to_nat (len + n)) bs = old ++ src))
       \/ (r = UPNP_E_OUTOF_MEMORY /\ B' = B /\ A' = A /\ cap' = cap /\ mbuf_rep_bytes m' MB B A len cap bs /\ firstn (Z.to_nat len) bs = old) ).
Definition membuffer_insert_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX B : list hblock) (MB A len cap S n lo : Z)
         (bs0 old src : list byte) (errv : word) (AB : Z),
  RHEAPx s (B ++ LBX) m -> env_ok m sp tp lo errv AB -> lo <= bv_unsigned sp - (64 + 8192) ->
  mbuf_rep_bytes m MB B A len cap bs0 -> firstn (Z.to_nat len) bs0 = old -> MB mod 8 = 0 ->
  (bv_unsigned sp <= MB \/ in_block LBX MB) ->
  bytes_at segs m S src -> zlength src = n -> 0 <= n -> len + n < 2^32 -> S <> 0 ->
  src_ok LBX (bv_unsigned sp) S n ->
  a0 = wz MB -> a1 = wz S -> a2 = wz n -> a3 = wz len ->
  SREACHx
    (membuffer_insert_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX B MB A len cap n lo AB old src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_membuffer_insert HA)) fc None m (seg_rom segs))
    s (B ++ LBX).

Definition membuffer_delete_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LBX B : list hblock) (MB A len cap i k lo AB : Z) (m : mem) : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (B' : list hblock) (A' len' cap' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' LBX sp tp lo [(MB, MB + 32)] AB
    /\ RHEAPx s' LB' m' /\ Permutation LB' (B' ++ LBX) /\ length B' = length B
    /\ mbuf_rep m' MB B' A' len' cap'
    /\ (len' = len - k \/ (len' = len /\ B' = B /\ A' = A /\ cap' = cap)).
Definition membuffer_delete_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX B : list hblock) (MB A len cap i k lo : Z) (errv : word) (AB : Z),
  RHEAPx s (B ++ LBX) m -> env_ok m sp tp lo errv AB -> lo <= bv_unsigned sp - (32 + 8192) ->
  mbuf_rep m MB B A len cap -> MB mod 8 = 0 -> (bv_unsigned sp <= MB \/ in_block LBX MB) ->
  0 <= i -> 0 <= k -> i + k <= len ->
  a0 = wz MB -> a1 = wz i -> a2 = wz k ->
  SREACHx
    (membuffer_delete_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX B MB A len cap i k lo AB m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_membuffer_delete HA)) fc None m (seg_rom segs))
    s (B ++ LBX).

Definition membuffer_destroy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LBX : list hblock) (MB lo AB : Z) (m : mem) : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' LBX sp tp lo [(MB, MB + 32)] AB
    /\ RHEAPx s' LB' m' /\ LB' = LBX
    /\ rw_cells segs m' MB (mbuf_cells 0 0 0).
Definition membuffer_destroy_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX B : list hblock) (MB A len cap lo : Z) (errv : word) (AB : Z),
  RHEAPx s (B ++ LBX) m -> env_ok m sp tp lo errv AB -> lo <= bv_unsigned sp - (16 + 8192) ->
  mbuf_rep m MB B A len cap -> MB mod 8 = 0 -> MB <> 0 -> (bv_unsigned sp <= MB \/ in_block LBX MB) ->
  a0 = wz MB ->
  SREACHx
    (membuffer_destroy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX MB lo AB m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_membuffer_destroy HA)) fc None m (seg_rom segs))
    s (B ++ LBX).

Definition ListFind_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : Z) (hs : list hdr) (id : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' (bv_unsigned sp - 48) (bv_unsigned sp)
    /\ (r = 0 \/ exists h N, In h hs /\ h_id h = id /\ r = N /\ N <> 0
           ).

Definition ListAddTail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LBX NB HBS HB : list hblock) (L lo AB : Z) (hs : list hdr) (h : hdr) (m : mem) : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' (HBS ++ HB ++ LBX) sp tp lo [(L, L + LINKEDLIST_SIZEOF)] AB

    /\ RHEAPx s' LB' m'
    /\ ( (r = 0 /\ Permutation LB' (NB ++ HBS ++ HB ++ LBX) /\ hlist_rep m' L NB HBS hs [] 0%nat /\ hdr_rep m' HB h)
       \/ (exists nb, r = blk_addr nb /\ r <> 0 /\ Permutation LB' (NB ++ [nb] ++ HBS ++ HB ++ LBX)
             /\ hlist_rep m' L (NB ++ [nb]) (HBS ++ HB) (hs ++ [h]) [] 0%nat) ).

Definition ListDestroy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LBX : list hblock) (L lo AB : Z) (m : mem) : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' LBX sp tp lo [(L, L + LINKEDLIST_SIZEOF)] AB
    /\ RHEAPx s' LB' m' /\ LB' = LBX
    /\ (exists first last c11 c12 : word, rw_cells segs m' L
          [C8 (wz 0); C8 first; C8 (wz 0); C8 last; C8 (wz 0); C8 (wz 0); C8 (wz 0);
           C8 (wz 0); C8 (wz LISTNODE_SIZEOF); C4 (wz FREELISTSIZE); C4 (wz 0); C8 c11; C8 c12]).

Definition parser_pre (m : mem) (s : PState) (LBX PB : list hblock) (P : Z) (st : pst) (sp tp : word) (lo : Z) (errv : word) (AB : Z) : Prop :=
  RHEAPx s (PB ++ LBX) m /\ parser_rep m P PB st /\ env_ok m sp tp lo errv AB
  /\ bv_unsigned sp <= P /\ P + PARSER_SIZEOF < 2^63 /\ P mod 8 = 0.

Definition parser_post_generic (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LBX : list hblock) (P lo AB : Z) (st : pst) (m : mem)
    (R : Z -> pst -> Prop)
    : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (PB' : list hblock) (st' : pst),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' LBX sp tp lo [(P, P + PARSER_SIZEOF)] AB
    /\ RHEAPx s' LB' m' /\ Permutation LB' (PB' ++ LBX)
    /\ parser_rep m' P PB' st'
    /\ R r st'.

Definition R_responseline (st : pst) (r : Z) (st' : pst) : Prop :=
  (r = PARSE_OK /\ p_position st' = POS_HEADERS) \/ (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE \/ r = PARSE_NO_MATCH).

Definition R_headers (st : pst) (r : Z) (st' : pst) : Prop :=
  p_cursor st <= p_cursor st' /\ p_msgLen st' = p_msgLen st /\ p_msgA st' = p_msgA st /\ p_estart st' = p_estart st
  /\ ( (r = PARSE_OK /\ p_position st' = POS_ENTITY)
     \/ (r = PARSE_SUCCESS /\ p_position st' = POS_COMPLETE)
     \/ (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE \/ r = PARSE_NO_MATCH) ).
Definition R_get_entity_read_method (st : pst) (r : Z) (st' : pst) : Prop :=
  p_cursor st' = p_cursor st /\ p_estart st' = p_cursor st /\ p_msgLen st' = p_msgLen st
  /\ ( (r = PARSE_SUCCESS) \/ (r = PARSE_FAILURE)
     \/ (r = PARSE_CONTINUE_1 /\ (p_entpos st' = ENTREAD_USING_CHUNKED \/ p_entpos st' = ENTREAD_USING_CLEN \/ p_entpos st' = ENTREAD_UNTIL_CLOSE)) ).
Definition R_entity (st : pst) (r : Z) (st' : pst) : Prop :=
  r <> PARSE_OK.
Definition R_parse (st : pst) (r : Z) (st' : pst) : Prop := r <> PARSE_OK.
Definition R_request_line (st : pst) (r : Z) (st' : pst) : Prop :=
  (r = PARSE_OK /\ p_position st' = POS_HEADERS) \/ (r = PARSE_SUCCESS /\ p_position st' = POS_COMPLETE)
  \/ (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE \/ r = PARSE_NO_MATCH).

Definition parser_parse_headers_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX PB : list hblock) (P lo : Z) (st : pst) (errv : word) (AB : Z),
  parser_pre m s LBX PB P st sp tp lo errv AB -> lo <= bv_unsigned sp - (240 + 64 + 208 + 96 + 8192) ->
  p_msgA st <> 0   ->
  zlength (p_hdrs st) + p_msgLen st < 2^40 ->
  a0 = wz P ->
  SREACHx
    (parser_post_generic ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX P lo AB st m (R_headers st))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz (ha_parser_parse_headers HA)) fc None m (seg_rom segs))
    s (PB ++ LBX).

Definition parser_parse_responseline_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX PB : list hblock) (P lo : Z) (st : pst) (errv : word) (AB : Z),
  parser_pre m s LBX PB P st sp tp lo errv AB -> lo <= bv_unsigned sp - (80 + 1600   + 8192) ->
  statusline_walk_ok ->
  a0 = wz P ->
  SREACHx
    (parser_post_generic ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX P lo AB st m (R_responseline st))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz (ha_parser_parse_responseline HA)) fc None m (seg_rom segs))
    s (PB ++ LBX).

Definition parser_get_entity_read_method_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX PB : list hblock) (P lo : Z) (st : pst) (errv : word) (AB : Z),
  parser_pre m s LBX PB P st sp tp lo errv AB -> lo <= bv_unsigned sp - (144 + 48 + 2300   + 400) ->
  p_msgA st <> 0 ->
  a0 = wz P ->

  SREACHx
    (parser_post_generic ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX P lo AB st m (R_get_entity_read_method st))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz (ha_parser_get_entity_read_method HA)) fc None m (seg_rom segs))
    s (PB ++ LBX).

Definition parser_parse_entity_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX PB : list hblock) (P lo : Z) (st : pst) (errv : word) (AB : Z),
  parser_pre m s LBX PB P st sp tp lo errv AB -> lo <= bv_unsigned sp - (144 + 240 + 64 + 208 + 96 + 8192) ->
  p_msgA st <> 0 -> p_position st = POS_ENTITY ->
  a0 = wz P ->
  SREACHx
    (parser_post_generic ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX P lo AB st m (R_entity st))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz (ha_parser_parse_entity HA)) fc None m (seg_rom segs))
    s (PB ++ LBX).

Definition parser_parse_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX PB : list hblock) (P lo : Z) (st : pst) (errv : word) (AB : Z),
  parser_pre m s LBX PB P st sp tp lo errv AB -> lo <= bv_unsigned sp - (208 + 144 + 240 + 64 + 208 + 96 + 8192) ->
  statusline_walk_ok ->
  a0 = wz P ->
  SREACHx
    (parser_post_generic ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX P lo AB st m (R_parse st))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz (ha_parser_parse HA)) fc None m (seg_rom segs))
    s (PB ++ LBX).

Definition fresh_pst (is_request position request_method : Z) : pst :=
  mkPst 0 request_method 0 is_request 0 0  0 0 0  0  []  0 0  0 0 0  0  400 0 position ENTREAD_DETERMINE_READ_METHOD 0 0 0  0.
Definition parser_append_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX : list hblock) (P D n lo : Z) (st : pst)
         (data : list byte) (errv : word) (AB : Z),
  parser_pre m s LBX [] P st sp tp lo errv AB -> lo <= bv_unsigned sp - (16 + 208 + 144 + 240 + 64 + 208 + 96 + 8192) ->
  (st = fresh_pst 1 POS_REQUEST_LINE 0 \/ st = fresh_pst 0 POS_RESPONSE_LINE 2  ) ->
  bytes_at segs m D data -> zlength data = n -> 0 <= n < 2^26 + 16 -> in_block LBX D   ->
  statusline_walk_ok ->
  a0 = wz P -> a1 = wz D -> a2 = wz n ->
  SREACHx
    (parser_post_generic ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX P lo AB st m (fun r st' => True))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz (ha_parser_append HA)) fc None m (seg_rom segs))
    s LBX.

Definition parser_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (st : pst) (fr : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - fr, bv_unsigned sp); (P, P + PARSER_SIZEOF)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' (bv_unsigned sp - fr) (bv_unsigned sp)
    /\ parser_rep m' P [] st.
Definition parser_request_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z) (junk : list byte),
  rw_cells segs m P [CB 504%nat junk] -> P mod 8 = 0 -> bv_unsigned sp <= P -> P + 504 < 2^63 ->
  stk segs m (bv_unsigned sp - 32) (bv_unsigned sp) -> mem_inv segs m ->
  a0 = wz P ->
  evt segs (parser_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (fresh_pst 1 POS_REQUEST_LINE 0) 32 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_parser_request_init HA)) fc None m (seg_rom segs)).
Definition parser_response_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z) (junk : list byte),
  rw_cells segs m P [CB 504%nat junk] -> P mod 8 = 0 -> bv_unsigned sp <= P -> P + 504 < 2^63 ->
  stk segs m (bv_unsigned sp - 48) (bv_unsigned sp) -> mem_inv segs m ->
  a0 = wz P -> a1 = wz 2 ->
  evt segs (parser_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (fresh_pst 0 POS_RESPONSE_LINE 2) 48 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_parser_response_init HA)) fc None m (seg_rom segs)).

Definition httpmsg_destroy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LBX : list hblock) (P lo AB : Z) (m : mem) : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' LBX sp tp lo [(P, P + PARSER_SIZEOF)] AB
    /\ RHEAPx s' LB' m' /\ LB' = LBX
    /\ rw_cells segs m' P [CB 504%nat junk].
Definition httpmsg_destroy_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX PB : list hblock) (P lo : Z) (st : pst) (errv : word) (AB : Z),
  parser_pre m s LBX PB P st sp tp lo errv AB -> lo <= bv_unsigned sp - (16 + 64 + 48 + 8192) ->
  a0 = wz P ->
  SREACHx
    (httpmsg_destroy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX P lo AB m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_httpmsg_destroy HA)) fc None m (seg_rom segs))
    s (PB ++ LBX).

Definition LLVMFuzzerTestOneInput_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LBX : list hblock) (lo AB : Z) (m : mem) : PState -> list hblock -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ aframe m m' LBX sp tp lo [] AB
    /\ RHEAPx s' LB' m' /\ LB' = LBX.
Definition LLVMFuzzerTestOneInput_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBX : list hblock) (D n lo : Z) (data : list byte) (errv : word) (AB : Z),
  RHEAPx s LBX m -> env_ok m sp tp lo errv AB -> lo <= bv_unsigned sp - (528 + 16 + 208 + 144 + 240 + 64 + 208 + 96 + 8192) ->
  bytes_at segs m D data -> zlength data = n -> 0 <= n < 2^26 + 16 ->
  (n = 0 \/ in_block LBX D) -> D <> 0 -> D + n < 2^63 ->
  statusline_walk_ok ->
  a0 = wz D -> a1 = wz n ->
  SREACHx
    (LLVMFuzzerTestOneInput_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBX lo AB m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_LLVMFuzzerTestOneInput HA)) fc None m (seg_rom segs))
    s LBX.

Definition parse_uri_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (U n OUT fr : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (junk : list byte) (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - fr, bv_unsigned sp); (OUT, OUT + URI_SIZEOF); (errno_addr tp, errno_addr tp + 4)] m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' (bv_unsigned sp - fr) (bv_unsigned sp)
    /\ rw_cells segs m' OUT [CB 216%nat junk]
    /\ rw_cells segs m' (errno_addr tp) [C4 errv']
    /\ (r = HTTP_SUCCESS \/ r = UPNP_E_INVALID_URL).
Definition parse_uri_stmt (fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (U n OUT : Z) (url slack ojunk : list byte) (errv : word) (AB : Z),
  bytes_at segs m U (url ++ Z_to_bv 8 0 :: slack) -> zlength url = n -> 1 <= n < 2^31 - 256 ->
  ((- (U + n + 1)) mod 8 <= zlength slack) ->
  rw_cells segs m OUT [CB 216%nat ojunk] -> OUT mod 8 = 0 -> bv_unsigned sp <= OUT ->
  (U + n + 1 + 8 <= bv_unsigned sp - fr)   ->
  rw_cells segs m (errno_addr tp) [C4 errv] -> GD m -> mem_inv segs m ->
  stk segs m (bv_unsigned sp - fr) (bv_unsigned sp) ->
  a0 = wz U -> a1 = wz n -> a2 = wz OUT ->
  evt segs (parse_uri_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc U n OUT fr m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_parse_uri HA)) fc None m (seg_rom segs)).

Definition parse_uric_stmt (fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (U n TOK : Z) (bs : list byte) (tj : list cell),
  bytes_at segs m U bs -> zlength bs = n -> 0 <= n < 2^62 -> U <> 0 -> U + n < 2^63 ->
  rw_cells segs m TOK tj -> cells_size tj = 16%nat -> TOK mod 8 = 0 -> bv_unsigned sp <= TOK ->
  mem_inv segs m -> stk segs m (bv_unsigned sp - fr) (bv_unsigned sp) ->
  a0 = wz U -> a1 = wz n -> a2 = wz TOK ->
  evt segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (i : Z),
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz i) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' (seg_rom segs)
              /\ munch [(bv_unsigned sp - fr, bv_unsigned sp); (TOK, TOK + 16)] m m' /\ wmono segs m m' /\ mem_inv segs m'
              /\ stk segs m' (bv_unsigned sp - fr) (bv_unsigned sp)
              /\ rw_cells segs m' TOK [C8 (wz U); C8 (wz i)]
              /\ 0 <= i <= n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_parse_uric HA)) fc None m (seg_rom segs)).

End REP.

