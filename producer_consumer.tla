\* simple model is a a queue with a certain ttl set on it.
\* it will be deleted after a certain amount of time has passed where it is unused.
\* we can have at least 1 producer, and 1 consumer on the queue.
\* a consumer can consumer from the queue, or remove things from the queue if its not empty
\* a producer can put something onto the queue if it's not full.
\* the producer and consumer need to wait for each other

