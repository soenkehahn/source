use std::fs;
use std::io::BufReader;
use std::path::Path;
use utf8_chars::BufReadCharsExt;

pub struct Stream<A: 'static>(Box<dyn FnOnce() -> Option<(A, Stream<A>)> + 'static>);

impl<A: 'static> Stream<A> {
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<A> {
        let original = std::mem::replace(&mut self.0, Box::new(|| None));
        match original() {
            Some((next_element, next_stream)) => {
                self.0 = next_stream.0;
                Some(next_element)
            }
            None => None,
        }
    }

    pub fn new<F: FnMut() -> Option<A> + 'static>(mut function: F) -> Stream<A> {
        Stream(Box::new(move || match function() {
            Some(next) => Some((next, Stream::new(function))),
            None => None,
        }))
    }

    pub fn empty() -> Stream<A> {
        Stream(Box::new(|| None))
    }

    pub fn single(a: A) -> Stream<A> {
        Stream(Box::new(|| Some((a, Stream::empty()))))
    }

    pub fn map<B, F: FnMut(A) -> B + 'static>(mut self, mut function: F) -> Stream<B> {
        Stream::new(move || match self.next() {
            Some(x) => Some(function(x)),
            None => None,
        })
    }

    pub fn filter<F: FnMut(&A) -> bool + 'static>(mut self, mut function: F) -> Stream<A> {
        Stream::new(move || loop {
            match self.next() {
                Some(a) if function(&a) => return Some(a),
                Some(_) => {}
                None => return None,
            }
        })
    }

    pub fn fold<Accumulator, F: FnMut(Accumulator, A) -> Accumulator>(
        self,
        initial: Accumulator,
        mut function: F,
    ) -> Accumulator {
        let mut accumulator = initial;
        for a in self {
            accumulator = function(accumulator, a);
        }
        accumulator
    }

    pub fn flat_map<B, Next: FnMut(A) -> Stream<B> + 'static>(self, next: Next) -> Stream<B> {
        self.map(next).flatten()
    }

    pub fn concat(self, other: Stream<A>) -> Stream<A> {
        Stream(Box::new(move || match self.0() {
            Some((a, next)) => Some((a, next.concat(other))),
            None => other.0(),
        }))
    }

    pub fn append(self, last: A) -> Stream<A> {
        self.concat(Stream::single(last))
    }

    pub fn prepend(self, head: A) -> Stream<A> {
        Stream(Box::new(|| Some((head, self))))
    }

    pub fn count<F: Fn(A) -> bool>(self, predicate: F) -> i32 {
        self.fold(0, |count, a| if predicate(a) { count + 1 } else { count })
    }
}

impl<A, I: Iterator<Item = A> + 'static> From<I> for Stream<A> {
    fn from(mut iterator: I) -> Self {
        Stream::new(move || iterator.next())
    }
}

impl<A> Stream<Stream<A>> {
    pub fn flatten(mut self) -> Stream<A> {
        let mut current = Stream::empty();
        Stream::new(move || loop {
            match current.next() {
                Some(a) => return Some(a),
                None => match self.next() {
                    Some(next_chunk) => {
                        current = next_chunk;
                    }
                    None => return None,
                },
            }
        })
    }
}

impl<A: Clone> Stream<A> {
    pub fn peek(&mut self) -> Option<A> {
        match self.next() {
            Some(a) => {
                let original = std::mem::replace(self, Stream::empty());
                *self = original.prepend(a.clone());
                Some(a)
            }
            None => None,
        }
    }

    pub fn replicate(n: u32, element: A) -> Stream<A> {
        let mut counter = 0;
        Stream::new(move || {
            if counter < n {
                counter += 1;
                Some(element.clone())
            } else {
                None
            }
        })
    }
}

impl Stream<char> {
    pub fn read_utf8_file(file: &Path) -> Result<Stream<char>, std::io::Error> {
        let mut file = BufReader::new(fs::File::open(file)?);
        Ok(Stream::new(move || {
            file.read_char().expect("utf8 decoding error")
        }))
    }
}

impl<Snippet: Into<Box<str>>> Stream<Snippet> {
    pub fn join<Separator: Into<Box<str>>>(self, separator: Separator) -> String {
        let separator: &str = &separator.into();
        let mut first = true;
        let mut result = "".to_string();
        for string in self {
            if !first {
                result.push_str(separator);
            } else {
                first = false;
            }
            result.push_str(&string.into());
        }
        result
    }
}

impl<A> IntoIterator for Stream<A> {
    type Item = A;
    type IntoIter = StreamIterator<A>;
    fn into_iter(self) -> StreamIterator<A> {
        StreamIterator(self)
    }
}

pub struct StreamIterator<A: 'static>(Stream<A>);

impl<A> Iterator for StreamIterator<A> {
    type Item = A;

    fn next(&mut self) -> Option<A> {
        self.0.next()
    }
}

#[macro_export]
macro_rules! stream {
    ($($x:expr),*) => {
        $crate::Stream::from(vec![$($x),*].into_iter())
    };
    ($($x:expr,)*) => {
        stream![$($x),*]
    };
    ($element:expr; $n:expr) => {
        $crate::Stream::replicate($n, $element)
    };
}

impl<A: ToString> Stream<A> {
    pub fn into_string(self) -> String {
        let mut first = true;
        let mut result = "stream![".to_string();
        for a in self {
            if !first {
                result.push_str(", ");
            } else {
                first = false;
            }
            result.push_str(&a.to_string());
        }
        result.push_str("]");
        result
    }
}

#[cfg(test)]
mod test {
    use super::*;

    impl<A> Stream<A> {
        pub fn to_vec(self) -> Vec<A> {
            self.into_iter().collect()
        }
    }

    mod conversions {
        use super::*;

        #[test]
        fn allows_to_convert_from_iterator() {
            let iter = vec![1, 2, 3].into_iter();
            let from_next = Stream::from(iter);
            assert_eq!(from_next.to_vec(), vec![1, 2, 3]);
        }

        #[test]
        fn allows_to_convert_into_iterator() {
            let stream = stream!(1, 2, 3).into_iter();
            assert_eq!(stream.collect::<Vec<_>>(), vec![1, 2, 3]);
        }
    }

    mod stream_macro {
        use super::*;

        #[test]
        fn allows_to_convert_from_elements() {
            let stream: Stream<i32> = stream![1, 2, 3];
            assert_eq!(stream.to_vec(), vec![1, 2, 3]);
        }

        #[test]
        fn allows_to_create_empty_streams() {
            let stream: Stream<i32> = Stream::empty();
            assert_eq!(stream.to_vec(), vec![]);
        }

        #[test]
        fn allows_to_create_streams_with_one_element() {
            let stream = Stream::single("foo");
            assert_eq!(stream.to_vec(), vec!["foo"]);
        }

        #[test]
        fn allows_to_trailing_commas() {
            let stream: Stream<i32> = stream![1, 2, 3,];
            assert_eq!(stream.to_vec(), vec![1, 2, 3]);
        }

        #[test]
        fn allows_to_replicate_a_given_element() {
            let stream: Stream<i32> = stream![42; 3];
            assert_eq!(stream.to_vec(), vec![42, 42, 42]);
        }
    }

    #[test]
    fn into_string_converts_into_stream_macro() {
        assert_eq!(stream![1, 2, 3].into_string(), "stream![1, 2, 3]");
        let empty: Stream<i32> = stream![];
        assert_eq!(empty.into_string(), "stream![]");
    }

    #[test]
    fn map_works() {
        let from_next: Stream<i32> = stream![1, 2, 3];
        let mapped = from_next.map(|x| x.pow(2));
        assert_eq!(vec![1, 4, 9], mapped.to_vec());
    }

    #[test]
    fn filter_works() {
        let stream = Stream::from(1..6).filter(|x| x % 2 == 1);
        assert_eq!(stream.to_vec(), vec![1, 3, 5]);
    }

    #[test]
    fn fold_works() {
        let sum = Stream::from(1..6).fold(0, |sum: i32, a| sum + a);
        assert_eq!(sum, 15);
    }

    #[test]
    fn flatten_works() {
        let flattened = stream!["foo", "bar"]
            .map(|x| Stream::from(x.chars()))
            .flatten();
        assert_eq!(vec!['f', 'o', 'o', 'b', 'a', 'r'], flattened.to_vec());
    }

    #[test]
    fn flatmap_works() {
        let stream = stream!["foo", "bar"].flat_map(|x| Stream::from(x.chars()));
        assert_eq!(vec!['f', 'o', 'o', 'b', 'a', 'r'], stream.to_vec());
    }

    #[test]
    fn concat_works() {
        let mut stream = stream!["foo", "bar"];
        stream = stream.concat(stream!["baz"]);
        assert_eq!(vec!["foo", "bar", "baz"], stream.to_vec());
    }

    #[test]
    fn append_works() {
        let mut stream = stream!["foo", "bar"];
        stream = stream.append("baz");
        assert_eq!(vec!["foo", "bar", "baz"], stream.to_vec());
    }

    #[test]
    fn prepend_works() {
        let stream = stream!["bar", "baz"].prepend("foo");
        assert_eq!(vec!["foo", "bar", "baz"], stream.to_vec());
    }

    mod peek {
        use super::*;

        #[test]
        fn peek_works() {
            let mut stream = stream!["foo", "bar"];
            assert_eq!(stream.peek(), Some("foo"));
            assert_eq!(vec!["foo", "bar"], stream.to_vec());
        }

        #[test]
        fn allows_to_peek_ahead() {
            let mut stream = Stream::from("x".chars());
            assert_eq!(stream.peek(), Some('x'));
        }

        #[test]
        fn peeking_does_not_consume_chars() {
            let mut stream = Stream::from("x".chars());
            stream.peek();
            assert_eq!(stream.next(), Some('x'));
        }

        #[test]
        fn peeking_works_twice() {
            let mut stream = Stream::from("ab".chars());
            stream.peek();
            assert_eq!(stream.peek(), Some('a'));
        }

        #[test]
        fn peeking_works_after_next() {
            let mut stream = Stream::from("ab".chars());
            stream.next();
            assert_eq!(stream.peek(), Some('b'));
        }
    }

    #[test]
    fn count_works() {
        let stream = stream![1, 2, 3, 4, 5, 6, 7];
        assert_eq!(stream.count(|x| x > 3), 4);
    }

    mod join {
        use super::*;

        #[test]
        fn works() {
            let stream = stream!("foo", "bar");
            assert_eq!(stream.join("#"), "foo#bar");
        }

        #[test]
        fn works_with_both_str_and_string() {
            let str_stream: Stream<&str> = stream!();
            str_stream.join("");
            let str_stream: Stream<&str> = stream!();
            str_stream.join("".to_string());
            let string_stream: Stream<String> = stream!();
            string_stream.join("");
            let string_stream: Stream<String> = stream!();
            string_stream.join("".to_string());
        }

        #[test]
        fn works_with_empty_inputs() {
            assert_eq!(stream!("", "foo").join("#"), "#foo");
            assert_eq!(stream!("foo", "").join("#"), "foo#");
            assert_eq!(stream!("", "foo", "").join("#"), "#foo#");
        }
    }
}
