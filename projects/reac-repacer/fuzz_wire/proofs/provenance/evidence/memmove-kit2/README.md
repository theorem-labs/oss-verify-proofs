# fuzz_wire __asan_memmove: the donor comparison re-run on the fixed comparison kit (kit2 = the second donor comparison of this record; the first is section 0 of memmove-A/GATES.md and memmove-B/GATES.md)

The memmove records memmove-A/ and memmove-B/ cite a closure, jtcheck and paircl comparison of fuzz_wire's __asan_memmove
against libreac/fuzz_pcap's released pins, made with repin_check 9cbc3553c09e, jtcheck 2e2f9c2126b2 and paircl
16e1466be22d. All three compared two differently named targets by content. This folder is the same comparison on the
fixed kit (records/kit-sha256.txt): paircl a88c2822a0f2 (registered), drvcmp over bytecmp 1480ca2faea0 and repin_check
e5487165abb8 (lines 188-247), and jtcheck with the fail-closed target rule (a different name, or a name on one side only,
is a difference with no content compare; its line 79).

Images: fuzz_wire.asan 2f8f8697cd4f (twin d2f662a22962), fuzz_wire.asan-ubsan af4534831a45 (twin 51eb4bef2425);
fuzz_pcap.asan b7a91d9b1fb0 (twin 36da3052c383), fuzz_pcap.asan-ubsan 9e66f771f22a (twin c969d83cdd59).

| image | closure (symbolic, against the twin) | jtcheck of the closure's other members | paircl (against the stripped pin, Y twin given) |
|---|---|---|---|
| A | 785 functions: EQUAL 173, EQUAL-mod-pcrel (all targets equal) 609, other 3 | 3 / 3: target differs 0, unpaired differing words 0 | 826 paired, 0 conflicts, other 14, named target differs 0 |
| B | 785 functions: EQUAL 171, EQUAL-mod-pcrel (all targets equal) 611, other 3 | 3 / 3: target differs 0, unpaired differing words 0 | 826 paired, 0 conflicts, other 14, named target differs 0 |

Verdict unchanged: the same code up to relocation, on both images. With the fixed kit the symbolic closure settles 8 more
members itself (other 11 -> 3). paircl's 14 'other' rows are functions whose pc-relative target is a jump table or a
constant pool longer than 8 bytes: the closure and jtcheck measure them by name. None is a named-target difference.

Commands (in the kit directory):

    python3 closure.py <wire twin> <pcap twin> __asan_memmove
    python3 jtcheck.py <wire twin> <pcap twin> <the closure's other members>
    python3 paircl.py <wire twin> <pcap pin> __asan_memmove <pcap entry: 51bf0 A / 51c40 B> <pcap twin>
